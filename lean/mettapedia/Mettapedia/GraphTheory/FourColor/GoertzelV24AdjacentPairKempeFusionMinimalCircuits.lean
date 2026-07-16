import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeFusionPortCircuit

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24AdjacentPairBoundary
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance]
  adjacentFusionLensRetainedVertexSetFintype
  adjacentFusionLensRetainedVertexSetDecidableEq

/-- A cyclic adjacent-pair profile in a graph-backed minimal counterexample
simultaneously supplies the two complementary fusion lenses and their exact
boundary-sensitive circuit alternatives. -/
theorem CyclicKempeProfile.exists_two_boundarySensitiveFusionCircuitOutcomes_of_minimal
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
        ((lens01.fusionSiteCount = 0 ∧
            ∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
              (circuit :
                (DeletedAdjacentPairGraph G data.firstVertex
                  data.secondVertex).Walk start start),
              circuit.IsCircuit ∧
              circuit.length = lens01.closedWalk.length ∧
              circuit.edges =
                lens01.closedWalk.support.tail.map Subtype.val ∧
              data.degreeTwoBoundaryData.defectVertex 0 ∈
                circuit.support ∧
              data.degreeTwoBoundaryData.defectVertex 1 ∈
                circuit.support) ∨
          (0 < lens01.fusionSiteCount ∧
            (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
                (circuit :
                  (DeletedAdjacentPairGraph G data.firstVertex
                    data.secondVertex).Walk start start),
                circuit.IsCircuit ∧
                circuit.length < lens01.closedWalk.length ∧
                data.degreeTwoBoundaryData.defectVertex 0 ∈
                  circuit.support) ∧
            (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
                (circuit :
                  (DeletedAdjacentPairGraph G data.firstVertex
                    data.secondVertex).Walk start start),
                circuit.IsCircuit ∧
                circuit.length < lens01.closedWalk.length ∧
                data.degreeTwoBoundaryData.defectVertex 1 ∈
                  circuit.support))) ∧
        ((lens23.fusionSiteCount = 0 ∧
            ∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
              (circuit :
                (DeletedAdjacentPairGraph G data.firstVertex
                  data.secondVertex).Walk start start),
              circuit.IsCircuit ∧
              circuit.length = lens23.closedWalk.length ∧
              circuit.edges =
                lens23.closedWalk.support.tail.map Subtype.val ∧
              data.degreeTwoBoundaryData.defectVertex 2 ∈
                circuit.support ∧
              data.degreeTwoBoundaryData.defectVertex 3 ∈
                circuit.support) ∨
          (0 < lens23.fusionSiteCount ∧
            (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
                (circuit :
                  (DeletedAdjacentPairGraph G data.firstVertex
                    data.secondVertex).Walk start start),
                circuit.IsCircuit ∧
                circuit.length < lens23.closedWalk.length ∧
                data.degreeTwoBoundaryData.defectVertex 2 ∈
                  circuit.support) ∧
            (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
                (circuit :
                  (DeletedAdjacentPairGraph G data.firstVertex
                    data.secondVertex).Walk start start),
                circuit.IsCircuit ∧
                circuit.length < lens23.closedWalk.length ∧
                data.degreeTwoBoundaryData.defectVertex 3 ∈
                  circuit.support))) := by
  rcases profile.exists_two_evenKempeFusionLenses_of_minimal
      minimal hab with
    ⟨C', hclosure, hC', hconstant, ⟨lens01⟩, ⟨lens23⟩⟩
  have hthird := third_color_properties hab.1 hab.2.1 hab.2.2
  have hac : a ≠ a + b := hthird.2.1.symm
  have hbc : b ≠ a + b := hthird.2.2.symm
  have houtcome01 :=
    lens01.fusionChain_portSpanningCircuit_or_endpointDefectShorterCircuits
      profile.boundaryWellFormed hab.2.2 hac hbc (by decide)
  have houtcome23 :=
    lens23.fusionChain_portSpanningCircuit_or_endpointDefectShorterCircuits
      profile.boundaryWellFormed hab.2.2 hac hbc (by decide)
  exact ⟨C', hclosure, hC', hconstant,
    lens01, lens23, houtcome01, houtcome23⟩

/-- The two complementary outcomes reduce to the structural endgame split:
either one lens has strict descents anchored at both endpoints, or both
complete lenses lift without loss to circuits spanning their port pairs. -/
theorem CyclicKempeProfile.exists_endpointAnchoredDescents_or_twoPortSpanningCircuits_of_minimal
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
        (((0 < lens01.fusionSiteCount ∧
              (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
                  (circuit : (DeletedAdjacentPairGraph G data.firstVertex
                    data.secondVertex).Walk start start),
                  circuit.IsCircuit ∧
                  circuit.length < lens01.closedWalk.length ∧
                  data.degreeTwoBoundaryData.defectVertex 0 ∈
                    circuit.support) ∧
              (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
                  (circuit : (DeletedAdjacentPairGraph G data.firstVertex
                    data.secondVertex).Walk start start),
                  circuit.IsCircuit ∧
                  circuit.length < lens01.closedWalk.length ∧
                  data.degreeTwoBoundaryData.defectVertex 1 ∈
                    circuit.support)) ∨
            (0 < lens23.fusionSiteCount ∧
              (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
                  (circuit : (DeletedAdjacentPairGraph G data.firstVertex
                    data.secondVertex).Walk start start),
                  circuit.IsCircuit ∧
                  circuit.length < lens23.closedWalk.length ∧
                  data.degreeTwoBoundaryData.defectVertex 2 ∈
                    circuit.support) ∧
              (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
                  (circuit : (DeletedAdjacentPairGraph G data.firstVertex
                    data.secondVertex).Walk start start),
                  circuit.IsCircuit ∧
                  circuit.length < lens23.closedWalk.length ∧
                  data.degreeTwoBoundaryData.defectVertex 3 ∈
                    circuit.support))) ∨
          (lens01.fusionSiteCount = 0 ∧
            lens23.fusionSiteCount = 0 ∧
            (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
              (circuit : (DeletedAdjacentPairGraph G data.firstVertex
                data.secondVertex).Walk start start),
              circuit.IsCircuit ∧
              circuit.length = lens01.closedWalk.length ∧
              circuit.edges =
                lens01.closedWalk.support.tail.map Subtype.val ∧
              data.degreeTwoBoundaryData.defectVertex 0 ∈
                circuit.support ∧
              data.degreeTwoBoundaryData.defectVertex 1 ∈
                circuit.support) ∧
            (∃ (start : retainedVertexSet data.firstVertex data.secondVertex)
              (circuit : (DeletedAdjacentPairGraph G data.firstVertex
                data.secondVertex).Walk start start),
              circuit.IsCircuit ∧
              circuit.length = lens23.closedWalk.length ∧
              circuit.edges =
                lens23.closedWalk.support.tail.map Subtype.val ∧
              data.degreeTwoBoundaryData.defectVertex 2 ∈
                circuit.support ∧
              data.degreeTwoBoundaryData.defectVertex 3 ∈
                circuit.support))) := by
  rcases profile.exists_two_boundarySensitiveFusionCircuitOutcomes_of_minimal
      minimal hab with
    ⟨C', hclosure, hC', hconstant,
      lens01, lens23, houtcome01, houtcome23⟩
  refine ⟨C', hclosure, hC', hconstant, lens01, lens23, ?_⟩
  rcases houtcome01 with hzero01 | hpositive01
  · rcases houtcome23 with hzero23 | hpositive23
    · exact Or.inr ⟨hzero01.1, hzero23.1,
        hzero01.2, hzero23.2⟩
    · exact Or.inl (Or.inr hpositive23)
  · exact Or.inl (Or.inl hpositive01)

end

end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
