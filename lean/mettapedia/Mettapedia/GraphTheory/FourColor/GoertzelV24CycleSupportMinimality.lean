import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24CycleEdgeSupportRigidity

/-!
# Minimal supports inside a simple cycle

The graph-theoretic core of the circuit--bond form of spherical separation is
that a nonempty union of cycles contained in one connected simple cycle must
be that whole cycle.  This file isolates that reusable statement before the
face-incidence consumer is introduced.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CycleSupportMinimality

open SimpleGraph
open GoertzelV24PrimalCycleSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If two finite graphs consist of cycles, the larger one is connected, and
the smaller is a nonempty subgraph of the larger, then they coincide. -/
theorem eq_of_le_of_isCycles_of_connected
    {small large : SimpleGraph V}
    (hsmall : small.IsCycles) (hlarge : large.IsCycles)
    (hconnected : large.Connected) (hle : small ≤ large)
    (hne : small ≠ ⊥) :
    small = large := by
  have hneighborEq : ∀ {vertex neighbor : V},
      small.Adj vertex neighbor →
        small.neighborSet vertex = large.neighborSet vertex := by
    intro vertex neighbor hadj
    apply Set.eq_of_subset_of_ncard_le
    · intro other hother
      exact hle hother
    · rw [hsmall ⟨neighbor, hadj⟩, hlarge ⟨neighbor, hle hadj⟩]
    · exact Set.toFinite _
  rcases (SimpleGraph.ne_bot_iff_exists_adj.mp hne) with
    ⟨root, rootNeighbor, hroot⟩
  apply le_antisymm hle
  intro left right hlargeEdge
  have hleftNonempty : (small.neighborSet left).Nonempty := by
    rcases hconnected root left with ⟨path⟩
    have hpropagate : ∀ {start finish : V},
        large.Walk start finish →
        (small.neighborSet start).Nonempty →
          (small.neighborSet finish).Nonempty := by
      intro start finish walk
      induction walk with
      | nil => exact fun h => h
      | @cons first second last hadj tail ih =>
          intro hfirst
          rcases hfirst with ⟨witness, hwitness⟩
          have hsets := hneighborEq hwitness
          have hstep : small.Adj first second := by
            change second ∈ small.neighborSet first
            rw [hsets]
            exact hadj
          exact ih ⟨first, hstep.symm⟩
    exact hpropagate path ⟨rootNeighbor, hroot⟩
  rcases hleftNonempty with ⟨neighbor, hneighbor⟩
  have hsets := hneighborEq hneighbor
  change right ∈ small.neighborSet left
  rw [hsets]
  exact hlargeEdge

/-- A nonzero binary cycle-space vector supported inside one ambient simple
cycle has exactly that cycle as its nonzero support. -/
theorem f2CycleSpace_support_eq_cycle_of_subset
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {root : V} (cycle : G.Walk root root) (hcycle : cycle.IsCycle)
    (chain : G.edgeSet → F2) (hchain : chain ∈ f2CycleSpace G)
    (hcubic : ∀ vertex : V, (incidentEdgeFinset G vertex).card = 3)
    (hsupport : ∀ edge : G.edgeSet, chain edge ≠ 0 →
      edge.1 ∈ cycle.edges)
    (anchor : G.edgeSet) (hanchor : chain anchor ≠ 0) :
    ∀ edge : G.edgeSet, chain edge ≠ 0 ↔ edge.1 ∈ cycle.edges := by
  have hflow : ∀ vertex : V,
      scalarVertexKirchhoffSum G chain vertex = 0 := by
    intro vertex
    exact scalarVertexKirchhoffSum_eq_zero_of_mem_f2CycleSpace
      hchain vertex
  rcases exists_isCycle_through_of_scalar_ne_zero
      chain hflow hcubic anchor hanchor with
    ⟨supportRoot, supportCycle, hsupportCycle, _hanchorCycle,
      hsupportCycleEdges⟩
  have hcycleSubset : supportCycle.edges ⊆ cycle.edges := by
    intro edge hedge
    let ambient : G.edgeSet :=
      ⟨edge, supportCycle.edges_subset_edgeSet hedge⟩
    exact hsupport ambient (hsupportCycleEdges ambient hedge)
  intro edge
  constructor
  · exact hsupport edge
  · intro hedge
    have hedgeSupportCycle : edge.1 ∈ supportCycle.edges :=
      (isCycle_mem_edges_iff_of_subset hcycle hsupportCycle
        hcycleSubset edge.1).1 hedge
    exact hsupportCycleEdges edge hedgeSupportCycle

end GoertzelV24CycleSupportMinimality

end Mettapedia.GraphTheory.FourColor
