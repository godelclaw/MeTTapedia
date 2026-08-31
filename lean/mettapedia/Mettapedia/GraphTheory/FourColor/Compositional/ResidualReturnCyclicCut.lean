import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnComplementaryCycle

/-!
# Cyclic cuts from nested residual returns

Two strictly nested physical returns determine disjoint simple cycles.  The
inner cycle is the exact face separator already constructed by the residual
return geometry; the outer cycle closes through the complementary carrier
arc.  Pushing the exact face cut away from the inner separator therefore
produces a literal cyclic edge cut with the same cubic width bound as the
underlying separator.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCyclicCut

open AlternatingSiteGeometry
open CyclePushOffCut
open GoertzelV24FaceDualConnectedness
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open ResidualReturnComplementaryCycle
open ResidualReturnTransversal
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two strictly nested physical returns produce a cyclic edge cut whose
width is bounded by three times the number of vertices on the inner
separator.  Nondegeneracy of both closed walks is automatic in a simple
graph. -/
theorem exists_bounded_cyclicEdgeCut_of_strictly_nested_returns
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hG : HasCubicIncidentEdgeTriples G)
    (sigma : Pairing V) (hSigma : sigma.SupportedBy G)
    {first second : V}
    (site : ProperAlternatingComponentWitness G sigma first second)
    (outer inner : OrderedReturnChord
      (orderedSiteReturnPairing hG sigma hSigma site))
    (hleft : outer.left < inner.left)
    (hright : inner.right < outer.right) :
    let separator := orderedReturnSeparator hG sigma hSigma site inner
    ∃ cut : ExactFaceCut rotation.toRotationSystem
        (fun edge : G.edgeSet => edge.1 ∈ separator.edges) F2,
      ∃ selected : F2,
        ∃ _realization : CyclicEdgeCutRealization G
            (CyclePushOffCut.edges rotation separator cut selected),
          (CyclePushOffCut.edges rotation separator cut selected).card ≤
            separator.support.toFinset.card * 3 := by
  dsimp only
  let separator := orderedReturnSeparator hG sigma hSigma site inner
  let outsideCycle := complementaryReturnCycle hG sigma hSigma site outer
  have hseparator : separator.IsCycle := by
    simpa only [separator] using orderedReturnSeparator_isCycle_automatic
      hG sigma hSigma site inner
  have houtside : outsideCycle.IsCycle := by
    simpa only [outsideCycle] using complementaryReturnCycle_isCycle
      hG sigma hSigma site outer
        (complementaryReturnCycle_length_alternative
          hG sigma hSigma site outer)
  have hdisjoint : outsideCycle.support.Disjoint separator.support := by
    simpa only [outsideCycle, separator] using
      complementaryReturnCycle_support_disjoint_orderedReturnSeparator
        hG sigma hSigma site outer inner hleft hright
  have hconnected : G.Connected := by
    rw [←
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
        G rotation]
    exact minimal.primalConnected
  have hdual := orbitFaceInteriorDual_connected rotation.toRotationSystem
    minimal.spherical.cubic minimal.primalConnected
      minimal.vertexRotationCyclic
  rcases exists_exactFaceCut_of_closedTrail
      rotation minimal.facesTwoSided hdual hconnected minimal.spherical
        separator hseparator.isTrail with
    ⟨cut, _hboundary⟩
  have hwidth : ∀ selected : F2,
      (CyclePushOffCut.edges rotation separator cut selected).card ≤
        separator.support.toFinset.card * 3 := by
    intro selected
    apply card_edges_le_support_mul_degreeBound
      rotation minimal.vertexRotationCyclic separator cut selected 3
    intro vertex _hvertex
    exact (incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
      hG vertex).le
  rcases exists_selected_with_complement_cycle_of_disjoint_cycle
      rotation minimal.vertexRotationCyclic separator cut outsideCycle
        houtside hdisjoint with
    ⟨selected, hcomplement⟩
  refine ⟨cut, selected,
    cyclicEdgeCutRealization_of_complement_cycle
      rotation separator hseparator cut selected hcomplement,
    hwidth selected⟩

end

end Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnCyclicCut
