import MettapediaFourColor.ConservedContract
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalTriangleFree
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientOneZeroFlow

/-!
# Actual singleton contract colourings from vertex minimality

The established planar adjacent-pair reduction supplies a colouring of the
two-vertex deletion. Its conserved singleton-zero extension integrates into
an actual contract colouring of the original source hypermap. The smaller-map
argument stays within graph-backed vertex minimality throughout.
-/

namespace FourColor.MinimalSingletonContract

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24MinimalTriangleFree
open GoertzelV24SimpleGraphTaitBridge GoertzelV24RotationVertexCutProfile
open GoertzelV24AdjacentPairBoundary GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open RotationConservedFacePotential
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G)

/-- The graph and rotation conservation laws sum the same incident edges. -/
theorem conserved_of_graph_flow (field : G.edgeSet → Mettapedia.GraphTheory.FourColor.Color)
    (flow : IsGraphFlow G field) : Conserved original.toRotationSystem field := by
  intro v
  have incident : original.toRotationSystem.incidentEdges v = incidentEdgeFinset G v := by
    ext e
    rw [GoertzelV24OrbitFaceCycleSpace.mem_toRotationSystem_incidentEdges_iff]
    simp [incidentEdgeFinset]
  change ∑ e ∈ original.toRotationSystem.incidentEdges v, field e = 0
  rw [incident]
  exact flow v

variable (minimal : GraphBackedVertexMinimalTaitCounterexample original)
include minimal

/-- A smaller planar cap supplies a conserved field with the selected edge
as its exact zero set. Every other original edge remains nonzero. -/
theorem one_zero (d : G.Dart) :
    ∃ field : G.edgeSet → Mettapedia.GraphTheory.FourColor.Color,
      Conserved original.toRotationSystem field ∧
      ∀ e, field e = 0 ↔ e = original.toRotationSystem.edgeOf d := by
  obtain ⟨data, first, second, _, C, hC, _⟩ :=
    exists_cyclicallyOrdered_deletedColoring_of_vertexMinimalTaitCounterexample
      original minimal d.adj
  have cubic := incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
    original minimal.spherical.cubic
  have noColour := graphBackedVertexMinimalTaitCounterexample_not_graphTaitColorable
    original minimal
  let field := oneZeroAmbientChain data C
  have flow : IsGraphFlow G field :=
    (oneZeroAmbientChain_isCDLGoodFlow_of_not_taitColorable data cubic noColour C hC).1
  have central : centralEdge data = original.toRotationSystem.edgeOf d := by
    apply Subtype.ext
    change s(data.firstVertex, data.secondVertex) = d.edge
    rw [first, second]
    rfl
  refine ⟨field, conserved_of_graph_flow original field flow, ?_⟩
  intro e
  exact (oneZeroAmbientChain_eq_zero_iff data cubic C hC e).trans (by rw [central])

/-- Every selected original dart has an actual singleton contract colouring.
This uses vertex minimality and its existing strict two-vertex reduction,
without assuming reference minimality or a complete colouring theorem. -/
theorem colorable (d : G.Dart) :
    (SourceConstruction.sourceMap original.toRotationSystem).CcColorable [d] := by
  obtain ⟨field, conserved, zeros⟩ := one_zero original minimal d
  obtain ⟨k, hk, _⟩ := ConservedContract.singleton original.toRotationSystem
    minimal.toBridgelessSphericalCubicMapData d field conserved zeros
  exact ⟨k, hk⟩

end
end FourColor.MinimalSingletonContract
