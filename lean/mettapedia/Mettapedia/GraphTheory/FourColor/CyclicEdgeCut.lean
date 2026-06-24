import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*}

/-- An edge crosses a vertex-side predicate when its two endpoints occur on opposite sides.
This is the graph-theoretic edge-cut predicate, independent of any planar embedding. -/
def EdgeCrossesVertexSide (G : SimpleGraph V) (side : V → Prop) (e : G.edgeSet) : Prop :=
  ∃ u v : V, u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V) ∧ side u ∧ ¬ side v

/-- A graph contains a cycle entirely on one side of a vertex-side predicate. -/
def HasCycleOnSide (G : SimpleGraph V) (side : V → Prop) : Prop :=
  ∃ u : V, side u ∧ ∃ p : G.Walk u u, p.IsCycle ∧ ∀ v, v ∈ p.support → side v

/-- A small cyclic edge cut: the finite edge cut induced by a vertex-side predicate has size at
most four, and both sides contain a cycle.  The CAP5 annulus argument should eventually construct
this from the planar/Jordan separator data. -/
structure SmallCyclicEdgeCut (G : SimpleGraph V) where
  edgeCut : Finset G.edgeSet
  side : V → Prop
  hcut_eq : ∀ e : G.edgeSet, e ∈ edgeCut ↔ EdgeCrossesVertexSide G side e
  hcard_le_four : edgeCut.card <= 4
  hinside_cycle : HasCycleOnSide G side
  houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)

theorem SmallCyclicEdgeCut.card_le_four {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    cut.edgeCut.card <= 4 :=
  cut.hcard_le_four

theorem SmallCyclicEdgeCut.edge_mem_iff {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G)
    (e : G.edgeSet) :
    e ∈ cut.edgeCut ↔ EdgeCrossesVertexSide G cut.side e :=
  cut.hcut_eq e

end Mettapedia.GraphTheory.FourColor
