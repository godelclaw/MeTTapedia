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

/-- Existence form for the manuscript's forbidden small cyclic edge cut. -/
def HasCyclicEdgeCutOfSizeAtMostFour (G : SimpleGraph V) : Prop :=
  ∃ cut : SmallCyclicEdgeCut G, cut.edgeCut.card <= 4

/-- Obstruction hypothesis used by the CAP5 exceptional-annulus branch: there is no cyclic edge
cut of size at most four. -/
def NoCyclicEdgeCutOfSizeAtMostFour (G : SimpleGraph V) : Prop :=
  ¬ HasCyclicEdgeCutOfSizeAtMostFour G

theorem SmallCyclicEdgeCut.hasCyclicEdgeCutOfSizeAtMostFour
    {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    HasCyclicEdgeCutOfSizeAtMostFour G :=
  ⟨cut, cut.hcard_le_four⟩

theorem NoCyclicEdgeCutOfSizeAtMostFour.not_smallCyclicEdgeCut
    {G : SimpleGraph V} (h : NoCyclicEdgeCutOfSizeAtMostFour G)
    (cut : SmallCyclicEdgeCut G) :
    False :=
  h cut.hasCyclicEdgeCutOfSizeAtMostFour

/-- A graph has cyclic edge-connectivity at least `k` when every cyclic edge cut has at least
`k` edges. -/
def CyclicEdgeConnectivityAtLeast (G : SimpleGraph V) (k : Nat) : Prop :=
  ∀ cut : SmallCyclicEdgeCut G, k <= cut.edgeCut.card

/-- The four-color minimal-counterexample hypothesis usually needed by the CAP5 annulus
argument: no cyclic edge cut of size at most four. -/
def CyclicallyFiveEdgeConnected (G : SimpleGraph V) : Prop :=
  CyclicEdgeConnectivityAtLeast G 5

theorem CyclicallyFiveEdgeConnected.noCyclicEdgeCutOfSizeAtMostFour
    {G : SimpleGraph V} (h : CyclicallyFiveEdgeConnected G) :
    NoCyclicEdgeCutOfSizeAtMostFour G := by
  intro hcut
  rcases hcut with ⟨cut, hcard⟩
  exact Nat.not_succ_le_self 4 (le_trans (h cut) hcard)

theorem NoCyclicEdgeCutOfSizeAtMostFour.cyclicallyFiveEdgeConnected
    {G : SimpleGraph V} (h : NoCyclicEdgeCutOfSizeAtMostFour G) :
    CyclicallyFiveEdgeConnected G := by
  intro cut
  by_contra hnot
  exact h ⟨cut, Nat.lt_succ_iff.mp (lt_of_not_ge hnot)⟩

theorem cyclicallyFiveEdgeConnected_iff_noCyclicEdgeCutOfSizeAtMostFour
    {G : SimpleGraph V} :
    CyclicallyFiveEdgeConnected G ↔ NoCyclicEdgeCutOfSizeAtMostFour G :=
  ⟨CyclicallyFiveEdgeConnected.noCyclicEdgeCutOfSizeAtMostFour,
    NoCyclicEdgeCutOfSizeAtMostFour.cyclicallyFiveEdgeConnected⟩

theorem CyclicallyFiveEdgeConnected.not_smallCyclicEdgeCut_card_le_four
    {G : SimpleGraph V} (h : CyclicallyFiveEdgeConnected G)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card <= 4) :
    False :=
  h.noCyclicEdgeCutOfSizeAtMostFour ⟨cut, hcard⟩

end Mettapedia.GraphTheory.FourColor
