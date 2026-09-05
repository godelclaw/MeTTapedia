import Mettapedia.GraphTheory.FourColor.TubeCorridorExclusion

/-!
# Literal shore nodes from tube sides (stage one)

The exclusion theorem `le_of_tube_nodes` takes literal shore nodes whose
majority vertex sides are the tube sides.  This file starts the construction
of those nodes from a tube: the edge shore of a vertex side is the set of
edges with both ends in the side, and for a *good* side — every inside vertex
sees at least two inside edges, every outside vertex at most one — the
majority vertex side of that shore is the side itself
(`majorityRetainedKeep_sideShore`).
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance tubeNodesEdgeSetFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance tubeNodesEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- the edge shore of a vertex side: edges with both ends in the side -/
noncomputable def sideShore (side : V → Prop) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun e => ∀ v ∈ (e : Sym2 V), side v

theorem mem_sideShore {side : V → Prop} {e : G.edgeSet} :
    e ∈ sideShore (G := G) side ↔ ∀ v ∈ (e : Sym2 V), side v := by
  classical
  simp [sideShore]

/-- a side whose shore has it as majority vertex side -/
structure GoodSide (side : V → Prop) : Prop where
  inside : ∀ v, side v → 2 ≤ (shoreIncidentEdges G (sideShore side) v).card
  outside : ∀ v, ¬ side v → (shoreIncidentEdges G (sideShore side) v).card ≤ 1

/-- **the majority vertex side of a good side's shore is the side** -/
theorem majorityRetainedKeep_sideShore {side : V → Prop} (h : GoodSide (G := G) side) :
    majorityRetainedKeep G (sideShore side) = side := by
  funext v
  apply propext
  rw [majorityRetainedKeep_iff]
  unfold majorityVertexSide
  constructor
  · intro h2
    by_contra hv
    have := h.outside v hv
    omega
  · exact h.inside v

end TubeSlab
end Mettapedia.GraphTheory.FourColor
