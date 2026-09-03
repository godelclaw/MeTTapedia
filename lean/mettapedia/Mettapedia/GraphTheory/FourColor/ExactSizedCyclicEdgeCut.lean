import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicThreeCutConnectedSides
import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutBoundaryOrder

/-!
# Cyclic edge cuts of one exact size

`SmallCyclicEdgeCut` hard-codes the cardinality bound four: it exists to
express the *absence* of small cuts.  The five-cut theorem needs to reason
about a cyclic cut that actually has five edges, which that structure cannot
represent — pairing it with a `card = 5` hypothesis is contradictory.  This
file provides the ring-size-parametric object: a cyclic edge cut of one
exact cardinality `n`, together with

* conversions to and from the bounded structure and realization data,
* the finite vertex side and its crossing-edge description, and
* the connected-shores theorem at exact size five: when the graph is
  cyclically five-edge-connected, both shores of an exact five-cut are
  connected — a component of one shore would otherwise induce a cyclic cut
  of at most four edges.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24CyclicThreeCutConnectedSides
open GoertzelV24FourEdgeCutBoundaryOrder
open GoertzelV24RotationVertexCutProfile
open GoertzelV24ThreeEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A cyclic edge cut with exactly `n` edges: the crossing edges of a vertex
side carrying a cycle, whose complement also carries a cycle. -/
structure ExactSizedCyclicEdgeCut (G : SimpleGraph V) (n : Nat) where
  edgeCut : Finset G.edgeSet
  side : V → Prop
  hcut_eq : ∀ e : G.edgeSet, e ∈ edgeCut ↔ EdgeCrossesVertexSide G side e
  hcard_eq : edgeCut.card = n
  hinside_cycle : HasCycleOnSide G side
  houtside_cycle : HasCycleOnSide G (fun v => ¬ side v)

namespace ExactSizedCyclicEdgeCut

/-- The same exact cut with the chosen side complemented. -/
def compl {n : Nat} (cut : ExactSizedCyclicEdgeCut G n) :
    ExactSizedCyclicEdgeCut G n where
  edgeCut := cut.edgeCut
  side := fun v => ¬ cut.side v
  hcut_eq := fun e =>
    (cut.hcut_eq e).trans (edgeCrossesVertexSide_compl G cut.side e).symm
  hcard_eq := cut.hcard_eq
  hinside_cycle := cut.houtside_cycle
  houtside_cycle :=
    HasCycleOnSide.mono (fun _ hv hnot => hnot hv) cut.hinside_cycle

/-- Forget the exact cardinality, retaining realization data. -/
def toCyclicEdgeCutRealization {n : Nat} (cut : ExactSizedCyclicEdgeCut G n) :
    CyclicEdgeCutRealization G cut.edgeCut where
  side := cut.side
  hcut_eq := cut.hcut_eq
  hinside_cycle := cut.hinside_cycle
  houtside_cycle := cut.houtside_cycle

/-- An exact cut of size at most four is a small cyclic edge cut. -/
def toSmallCyclicEdgeCut {n : Nat} (cut : ExactSizedCyclicEdgeCut G n)
    (hn : n ≤ 4) : SmallCyclicEdgeCut G where
  edgeCut := cut.edgeCut
  side := cut.side
  hcut_eq := cut.hcut_eq
  hcard_le_four := by rw [cut.hcard_eq]; exact hn
  hinside_cycle := cut.hinside_cycle
  houtside_cycle := cut.houtside_cycle

end ExactSizedCyclicEdgeCut

/-- A small cyclic edge cut of known cardinality is an exact-sized cut. -/
def SmallCyclicEdgeCut.toExactSized (cut : SmallCyclicEdgeCut G) {n : Nat}
    (hcard : cut.edgeCut.card = n) : ExactSizedCyclicEdgeCut G n where
  edgeCut := cut.edgeCut
  side := cut.side
  hcut_eq := cut.hcut_eq
  hcard_eq := hcard
  hinside_cycle := cut.hinside_cycle
  houtside_cycle := cut.houtside_cycle

/-- The finite vertex side of an exact-sized cyclic cut. -/
noncomputable def exactCutVertexSide {n : Nat} (cut : ExactSizedCyclicEdgeCut G n) :
    Finset V := by
  classical
  exact Finset.univ.filter cut.side

@[simp]
theorem mem_exactCutVertexSide_iff {n : Nat}
    (cut : ExactSizedCyclicEdgeCut G n) (vertex : V) :
    vertex ∈ exactCutVertexSide cut ↔ cut.side vertex := by
  classical
  simp [exactCutVertexSide]

/-- The endpoint-computed crossing edges of the finite selected side are
exactly the edge set carried by the exact cut. -/
theorem vertexSetCrossingEdges_exactCutVertexSide {n : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (cut : ExactSizedCyclicEdgeCut G n) :
    vertexSetCrossingEdges graphData.toRotationSystem
        (exactCutVertexSide cut) = cut.edgeCut := by
  ext edge
  rw [mem_simpleGraph_vertexSetCrossingEdges_iff]
  simpa [mem_exactCutVertexSide_iff] using (cut.hcut_eq edge).symm

section ConnectedShores

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **Connected shores at the connectivity threshold.**  In a connected graph
whose cyclic edge-connectivity is at least `n ≥ 5`, the chosen shore of an
exact cyclic `n`-cut is connected: the reachable component of the inside
cycle would otherwise induce a cyclic cut which is either small — against
connectivity — or already the full cut. -/
theorem induce_side_connected_of_exactSized
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5) :
    (G.induce cut.side).Connected := by
  classical
  rcases cut.hinside_cycle with
    ⟨root, hroot, walk, hcycle, hsupport⟩
  set component := inducedReachableSide G cut.side root hroot with hcomponent
  set componentEdges : Finset G.edgeSet := cut.edgeCut.filter
    (fun edge => EdgeCrossesVertexSide G component edge) with hcomponentEdges
  have hcomponent_cut_eq : ∀ e : G.edgeSet,
      e ∈ componentEdges ↔ EdgeCrossesVertexSide G component e := by
    intro edge
    rw [hcomponentEdges]
    simp only [Finset.mem_filter]
    constructor
    · exact fun hedge => hedge.2
    · intro hcross
      exact ⟨(cut.hcut_eq edge).2
          (edgeCrossesVertexSide_of_inducedReachableSide
            cut.side root hroot edge hcross),
        hcross⟩
  have hsubset : componentEdges ⊆ cut.edgeCut := Finset.filter_subset _ _
  have hcomponentCard : 5 ≤ componentEdges.card := by
    by_cases hsmall : componentEdges.card ≤ 4
    · exfalso
      have hbound := hcyclic
        { edgeCut := componentEdges
          side := component
          hcut_eq := hcomponent_cut_eq
          hcard_le_four := hsmall
          hinside_cycle :=
            hasCycleOnSide_inducedReachableSide cut.side root hroot
              walk hcycle hsupport
          houtside_cycle := HasCycleOnSide.mono
            (fun vertex houtside hcomp =>
              houtside (inducedReachableSide_mem hcomp))
            cut.houtside_cycle }
      have hbound' : 5 ≤ componentEdges.card := hbound
      omega
    · have hcardLe : componentEdges.card ≤ 5 := by
        have := Finset.card_le_card hsubset
        rw [cut.hcard_eq] at this
        exact this
      omega
  have hcutsEqual : componentEdges = cut.edgeCut := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [cut.hcard_eq]
    exact hcomponentCard
  have hall : ∀ vertex, cut.side vertex → component vertex := by
    intro vertex hvertex
    by_contra hnotComponent
    set otherComponent := inducedReachableSide G cut.side vertex hvertex
      with hotherComponent
    have hotherVertex : otherComponent vertex :=
      inducedReachableSide_root cut.side vertex hvertex
    have hnotOtherRoot : ¬ otherComponent root := by
      intro hotherRoot
      apply hnotComponent
      rcases hotherRoot with ⟨_hroot, hreachable⟩
      exact ⟨hvertex, by simpa using hreachable.symm⟩
    rcases hconnected vertex root with ⟨ambientWalk⟩
    rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
        otherComponent ambientWalk hotherVertex hnotOtherRoot with
      ⟨edge, _hedgeWalk, hcrossOther⟩
    have hcrossSide : EdgeCrossesVertexSide G cut.side edge :=
      edgeCrossesVertexSide_of_inducedReachableSide
        cut.side vertex hvertex edge hcrossOther
    have hedgeCut : edge ∈ cut.edgeCut := (cut.hcut_eq edge).2 hcrossSide
    have hedgeComponentCut : edge ∈ componentEdges := by
      rw [hcutsEqual]
      exact hedgeCut
    have hcrossComponent : EdgeCrossesVertexSide G component edge :=
      (hcomponent_cut_eq edge).1 hedgeComponentCut
    rcases hcrossOther with
      ⟨inner, outer, hinnerEdge, houterEdge, hinnerOther, houterOther⟩
    have hverticesNe : inner ≠ outer := by
      intro heq
      exact houterOther (heq ▸ hinnerOther)
    have hedgePair : (edge : Sym2 V) = s(inner, outer) :=
      sym2_eq_mk_of_mem_of_mem_of_ne
        hinnerEdge houterEdge hverticesNe
    have hinnerSide : cut.side inner :=
      inducedReachableSide_mem hinnerOther
    have houterNotSide : ¬ cut.side outer := by
      intro houterSide
      exact (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
        hedgePair hcrossSide)
        ⟨fun _ => houterSide, fun _ => hinnerSide⟩
    have hinnerNotComponent : ¬ component inner := by
      intro hinnerComponent
      apply hnotComponent
      rcases hinnerComponent with ⟨_hinnerSide, hrootInner⟩
      rcases hinnerOther with ⟨_hinnerSide', hvertexInner⟩
      exact ⟨hvertex, by simpa using hrootInner.trans hvertexInner.symm⟩
    have houterNotComponent : ¬ component outer := by
      intro houterComponent
      exact houterNotSide (inducedReachableSide_mem houterComponent)
    exact (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
      hedgePair hcrossComponent)
      ⟨fun hinnerComponent => (hinnerNotComponent hinnerComponent).elim,
        fun houterComponent => (houterNotComponent houterComponent).elim⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨root, hroot⟩, ?_⟩
  intro vertex
  rcases hall vertex.1 vertex.2 with ⟨_hvertex, hreachable⟩
  simpa using hreachable

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem induce_complement_connected_of_exactSized
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5) :
    (G.induce (fun vertex => ¬ cut.side vertex)).Connected := by
  change (G.induce cut.compl.side).Connected
  exact induce_side_connected_of_exactSized hconnected hcyclic cut.compl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Both shores of an exact five-cut are connected at cyclic five-edge
connectivity. -/
theorem induce_both_sides_connected_of_exactSized
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 5)
    (cut : ExactSizedCyclicEdgeCut G 5) :
    (G.induce cut.side).Connected ∧
      (G.induce (fun vertex => ¬ cut.side vertex)).Connected :=
  ⟨induce_side_connected_of_exactSized hconnected hcyclic cut,
    induce_complement_connected_of_exactSized hconnected hcyclic cut⟩

end ConnectedShores

end Mettapedia.GraphTheory.FourColor
