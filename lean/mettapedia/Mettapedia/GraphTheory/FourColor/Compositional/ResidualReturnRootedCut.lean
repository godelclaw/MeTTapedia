import Mettapedia.GraphTheory.FourColor.Compositional.CyclePushOffConnected
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnSeparatorFaceCut
import Mettapedia.GraphTheory.FourColor.Compositional.ResidualReturnComplementaryCycle
import Mettapedia.GraphTheory.FourColor.RootedCutSaturation

/-!
# Rooted connected cuts from nested residual returns

The ordinary residual-return cut interface forgets which complementary
cycle witnessed cyclicity.  A nested family needs that provenance: one
outer complementary cycle supplies a common exterior root, allowing rooted
saturation to preserve inclusion between all later shores.

This file retains the actual outer cycle, constructs the inner push-off cut,
and saturates it at that fixed exterior root.  No uniform width claim is made;
the bound remains three times the inner separator support.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace ResidualReturnRootedCut

open AlternatingSiteGeometry
open CyclePushOffCut
open GoertzelV24FaceDualConnectedness
open GoertzelV24ResidualReturnCycleOrder
open GoertzelV24ResidualReturnSectorNoncrossing
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.GraphTheory.Embedding
open ResidualReturnComplementaryCycle
open ResidualReturnSeparatorFaceCut
open RootedCutSaturation
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance finiteGraphLocallyFinite : G.LocallyFinite := fun vertex =>
  @Subtype.fintype V (Membership.mem (G.neighborSet vertex))
    (inferInstance : DecidablePred (Membership.mem (G.neighborSet vertex)))
    inferInstance

/-- A strictly nested pair yields a connected cut whose side contains the
literal filled side of the inner return separator.  The outer complementary
cycle is retained pointwise outside that literal side, so several such
receipts can share one exterior root. -/
theorem exists_rooted_connectedCut_of_strictly_nested_returns
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
    let outsideCycle := complementaryReturnCycle hG sigma hSigma site outer
    ∃ faceCut : ExactFaceCut rotation.toRotationSystem
        (fun edge : G.edgeSet => edge.1 ∈ separator.edges) F2,
      ∃ selected : F2,
        (∀ vertex, vertex ∈ outsideCycle.support →
          ¬faceCut.filledCycleSide rotation separator selected vertex) ∧
        ∃ raw : CyclicEdgeCutRealization G
            (CyclePushOffCut.edges rotation separator faceCut selected),
          (∀ vertex, raw.side vertex ↔
            faceCut.filledCycleSide rotation separator selected vertex) ∧
          (CyclePushOffCut.edges rotation separator faceCut selected).card ≤
            separator.support.toFinset.card * 3 ∧
          ∃ connected : CyclicEdgeCutRealization.ConnectedAtWidth G
              (separator.support.toFinset.card * 3),
            connected.edgeCut ⊆
              CyclePushOffCut.edges rotation separator faceCut selected ∧
            ∀ vertex,
              faceCut.filledCycleSide rotation separator selected vertex →
                connected.realization.side vertex := by
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
  rcases exists_exactFaceCut_orderedReturnSeparator rotation minimal hG sigma
      hSigma site inner with ⟨faceCut, _hboundary⟩
  rcases exists_selected_with_specific_complement_cycle
      rotation minimal.vertexRotationCyclic separator faceCut outsideCycle
        houtside hdisjoint with ⟨selected, houtsideSupport⟩
  refine ⟨faceCut, selected, houtsideSupport, ?_⟩
  have hcomplement : HasCycleOnSide G
      (fun vertex =>
        ¬faceCut.filledCycleSide rotation separator selected vertex) :=
    ⟨_, houtsideSupport _ outsideCycle.start_mem_support,
      outsideCycle, houtside, houtsideSupport⟩
  let raw := cyclicEdgeCutRealization_of_complement_cycle
    rotation separator hseparator faceCut selected hcomplement
  have hwidth :
      (CyclePushOffCut.edges rotation separator faceCut selected).card ≤
        separator.support.toFinset.card * 3 := by
    apply card_edges_le_support_mul_degreeBound
      rotation minimal.vertexRotationCyclic separator faceCut selected 3
    intro vertex _hvertex
    exact (incidentEdgeFinset_card_eq_three_of_hasCubicIncidentEdgeTriples
      hG vertex).le
  have hconnected : G.Connected := by
    rw [←
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
        G rotation]
    exact minimal.primalConnected
  have hrawConnected : (G.induce raw.side).Connected := by
    exact induce_filledCycleSide_connected rotation hconnected
      minimal.vertexRotationCyclic separator hseparator faceCut selected
  rcases RootedCutSaturation.exists_connectedAtWidth
      hconnected raw hrawConnected _
      (houtsideSupport _ outsideCycle.start_mem_support)
      outsideCycle houtside houtsideSupport _ hwidth with
    ⟨connected, hconnectedEdgeCut, hconnectedSide⟩
  refine ⟨raw, fun _ => Iff.rfl, hwidth, connected, ?_, ?_⟩
  · rw [hconnectedEdgeCut]
    exact RootedCutSaturation.edgeCut_subset raw _ _
  · intro vertex hvertex
    exact (hconnectedSide vertex).2
      (RootedCutSaturation.side_subset_closureSide raw.side _ _
        vertex hvertex)

end

end ResidualReturnRootedCut

end Mettapedia.GraphTheory.FourColor.Compositional
