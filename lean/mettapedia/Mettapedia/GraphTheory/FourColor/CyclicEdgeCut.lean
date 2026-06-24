import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*}

/-- An edge crosses a vertex-side predicate when its two endpoints occur on opposite sides.
This is the graph-theoretic edge-cut predicate, independent of any planar embedding. -/
def EdgeCrossesVertexSide (G : SimpleGraph V) (side : V → Prop) (e : G.edgeSet) : Prop :=
  ∃ u v : V, u ∈ (e : Sym2 V) ∧ v ∈ (e : Sym2 V) ∧ side u ∧ ¬ side v

/-- Crossing a vertex-side predicate is invariant under swapping the two sides. -/
theorem edgeCrossesVertexSide_compl (G : SimpleGraph V) (side : V → Prop) (e : G.edgeSet) :
    EdgeCrossesVertexSide G (fun v => ¬ side v) e ↔ EdgeCrossesVertexSide G side e := by
  classical
  constructor
  · rintro ⟨u, v, hu, hv, hnotSide, hnotNotSide⟩
    exact ⟨v, u, hv, hu, by_contra fun h => hnotNotSide h, hnotSide⟩
  · rintro ⟨u, v, hu, hv, hside, hnotSide⟩
    exact ⟨v, u, hv, hu, hnotSide, fun h => h hside⟩

/-- A graph contains a cycle entirely on one side of a vertex-side predicate. -/
def HasCycleOnSide (G : SimpleGraph V) (side : V → Prop) : Prop :=
  ∃ u : V, side u ∧ ∃ p : G.Walk u u, p.IsCycle ∧ ∀ v, v ∈ p.support → side v

/-- A cycle contained on one side remains contained after weakening that side predicate. -/
theorem HasCycleOnSide.mono {G : SimpleGraph V} {side₁ side₂ : V → Prop}
    (hside : ∀ v, side₁ v → side₂ v)
    (hcycle : HasCycleOnSide G side₁) :
    HasCycleOnSide G side₂ := by
  rcases hcycle with ⟨u, hu, p, hpcycle, hpside⟩
  exact ⟨u, hside u hu, p, hpcycle, fun v hv => hside v (hpside v hv)⟩

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

/-- The same cyclic cut with the chosen side complemented.  The edge support and cardinality are
unchanged; the inside/outside cycle witnesses swap. -/
def SmallCyclicEdgeCut.compl {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    SmallCyclicEdgeCut G where
  edgeCut := cut.edgeCut
  side := fun v => ¬ cut.side v
  hcut_eq := fun e =>
    (cut.hcut_eq e).trans (edgeCrossesVertexSide_compl G cut.side e).symm
  hcard_le_four := cut.hcard_le_four
  hinside_cycle := cut.houtside_cycle
  houtside_cycle :=
    HasCycleOnSide.mono (fun _ hv hnot => hnot hv) cut.hinside_cycle

@[simp]
theorem SmallCyclicEdgeCut.compl_edgeCut {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    cut.compl.edgeCut = cut.edgeCut :=
  rfl

@[simp]
theorem SmallCyclicEdgeCut.compl_card {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    cut.compl.edgeCut.card = cut.edgeCut.card :=
  rfl

/-- Realization data for a finite edge support as a cyclic edge cut.  This is the natural
target for planar/Jordan separator constructions: give the vertex side, prove exact crossing-edge
equality, and provide cycles on both sides.  A separate cardinality proof turns it into a
`SmallCyclicEdgeCut`. -/
structure CyclicEdgeCutRealization (G : SimpleGraph V) (edgeCut : Finset G.edgeSet) where
  side : V → Prop
  hcut_eq : ∀ e : G.edgeSet, e ∈ edgeCut ↔ EdgeCrossesVertexSide G side e
  hinside_cycle : HasCycleOnSide G side
  houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)

/-- Build a small cyclic edge cut from realization data plus the cardinality bound. -/
def CyclicEdgeCutRealization.toSmallCyclicEdgeCut
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card <= 4) :
    SmallCyclicEdgeCut G where
  edgeCut := edgeCut
  side := realization.side
  hcut_eq := realization.hcut_eq
  hcard_le_four := hcard
  hinside_cycle := realization.hinside_cycle
  houtside_cycle := realization.houtside_cycle

@[simp]
theorem CyclicEdgeCutRealization.toSmallCyclicEdgeCut_edgeCut
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card <= 4) :
    (realization.toSmallCyclicEdgeCut hcard).edgeCut = edgeCut :=
  rfl

/-- Complement the chosen side in a cyclic-cut realization without changing the finite edge
support. -/
def CyclicEdgeCutRealization.compl
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) :
    CyclicEdgeCutRealization G edgeCut where
  side := fun v => ¬ realization.side v
  hcut_eq := fun e =>
    (realization.hcut_eq e).trans (edgeCrossesVertexSide_compl G realization.side e).symm
  hinside_cycle := realization.houtside_cycle
  houtside_cycle :=
    HasCycleOnSide.mono (fun _ hv hnot => hnot hv) realization.hinside_cycle

@[simp]
theorem CyclicEdgeCutRealization.compl_toSmallCyclicEdgeCut_edgeCut
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card <= 4) :
    ((realization.compl).toSmallCyclicEdgeCut hcard).edgeCut =
      (realization.toSmallCyclicEdgeCut hcard).edgeCut :=
  rfl

/-- Existence form for the manuscript's forbidden small cyclic edge cut. -/
def HasCyclicEdgeCutOfSizeAtMostFour (G : SimpleGraph V) : Prop :=
  ∃ cut : SmallCyclicEdgeCut G, cut.edgeCut.card <= 4

/-- Realization data plus a size bound gives the corresponding small cyclic-edge-cut existence
form. -/
theorem CyclicEdgeCutRealization.hasCyclicEdgeCutOfSizeAtMostFour
    {G : SimpleGraph V} {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcard : edgeCut.card <= 4) :
    HasCyclicEdgeCutOfSizeAtMostFour G :=
  ⟨realization.toSmallCyclicEdgeCut hcard, hcard⟩

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
