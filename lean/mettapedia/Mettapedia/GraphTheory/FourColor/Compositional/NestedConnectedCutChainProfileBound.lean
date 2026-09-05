import Mettapedia.GraphTheory.FourColor.Compositional.PathPrefixConnectedCutProfileBound

/-!
# Profile-state bound for a strictly nested chain of connected cuts

The sealed prefix bound counts positions along a path whose prefixes
saturate to connected cuts; its proof shows the phased-state map is
injective on strictly nested shores in a least counterexample.  The path is
only a device for producing nested cuts.  This module states the bound
directly on the object the corridor labs produce: a family of connected
cuts at width `bound` whose incident-edge shores are pairwise strictly
nested (a chain).  The family has at most `pathPrefixProfileStateCount
bound` members.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace NestedConnectedCutChainProfileBound

open CyclicEdgeCutRealization
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24NormalizedShoreDescent
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open Mettapedia.GraphTheory
open PathPrefixBoundary
open PathPrefixCyclicCut
open PathPrefixRootedNesting
open RootedCutSaturation
open SimpleGraph
open SimpleGraphDartRotation
open PathPrefixConnectedCutProfileBound

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A strictly nested chain of connected cuts at width `bound` in a
graph-backed least counterexample has at most `pathPrefixProfileStateCount
bound` members: two nested cuts with equal phased state would splice to a
smaller counterexample. -/
theorem card_le_profileStateCount_of_nestedChain
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (bound : Nat) {ι : Type u} [Fintype ι]
    (cut : ι → ConnectedAtWidth G bound)
    (hchain : ∀ i j, i ≠ j →
      incidentEdgeShore G (cut i).realization.side ⊂
          incidentEdgeShore G (cut j).realization.side ∨
        incidentEdgeShore G (cut j).realization.side ⊂
          incidentEdgeShore G (cut i).realization.side) :
    Fintype.card ι ≤ pathPrefixProfileStateCount bound := by
  classical
  let nodes : ι → LiteralShoreNode rotation bound bound := fun i =>
    ((cut i).toConnectedShoreNode rotation minimal).toLiteral rotation minimal
  let state : ι → Fin (6 * bound + 1) × StateAtBound.{u} bound :=
    fun i => (nodes i).cardPhasedState
  have hshore : ∀ i, (nodes i).shore = incidentEdgeShore G (cut i).realization.side := by
    intro i
    simp only [nodes, ConnectedShoreNode.toLiteral_shore,
      ConnectedAtWidth.toConnectedShoreNode_shore]
  have hinj : Function.Injective state := by
    intro i j heq
    by_contra hne
    rcases hchain i j hne with h | h
    · have hproper : (nodes i).shore ⊂ (nodes j).shore := by
        rw [hshore i, hshore j]; exact h
      exact cardPhasedState_ne_of_ssubset rotation minimal (nodes j) (nodes i) hproper
        (by simpa only [state] using heq.symm)
    · have hproper : (nodes j).shore ⊂ (nodes i).shore := by
        rw [hshore i, hshore j]; exact h
      exact cardPhasedState_ne_of_ssubset rotation minimal (nodes i) (nodes j) hproper
        (by simpa only [state] using heq)
  have hcard := Fintype.card_le_of_injective state hinj
  simpa only [Fintype.card_prod, Fintype.card_fin, card_stateAtBound,
    pathPrefixProfileStateCount] using hcard

end

end NestedConnectedCutChainProfileBound

end Mettapedia.GraphTheory.FourColor.Compositional
