import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicThreeCutConnectedSides

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CyclicExactCutConnectedSides

open SimpleGraph
open GoertzelV24CyclicThreeCutConnectedSides

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In a connected graph, an exact cyclic cut attaining the established
cyclic-connectivity lower bound has connected induced sides. Otherwise the
component containing the named inside cycle would itself define a proper
subcut of the same minimum cardinality. -/
theorem induce_side_connected_of_card_eq
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G k)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = k) :
    (G.induce cut.side).Connected := by
  rcases cut.hinside_cycle with
    ⟨root, hroot, walk, hcycle, hsupport⟩
  let component := inducedReachableSide G cut.side root hroot
  have hall : ∀ vertex, cut.side vertex → component vertex := by
    intro vertex hvertex
    by_contra hnotComponent
    let componentCut :=
      inducedReachableCyclicCut cut root hroot walk hcycle hsupport
    have hsubset : componentCut.edgeCut ⊆ cut.edgeCut :=
      inducedReachableCyclicCut_edgeCut_subset
        cut root hroot walk hcycle hsupport
    have hcomponentCard : k ≤ componentCut.edgeCut.card := hcyclic componentCut
    have hcutsEqual : componentCut.edgeCut = cut.edgeCut := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [hcard]
      exact hcomponentCard
    let otherComponent :=
      inducedReachableSide G cut.side vertex hvertex
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
    have hedgeComponentCut : edge ∈ componentCut.edgeCut := by
      rw [hcutsEqual]
      exact hedgeCut
    have hcrossComponent : EdgeCrossesVertexSide G component edge :=
      (componentCut.hcut_eq edge).1 hedgeComponentCut
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
theorem induce_complement_connected_of_card_eq
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G k)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = k) :
    (G.induce (fun vertex => ¬ cut.side vertex)).Connected := by
  change (G.induce cut.compl.side).Connected
  exact induce_side_connected_of_card_eq
    hconnected hcyclic cut.compl hcard

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem induce_both_sides_connected_of_card_eq
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G k)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = k) :
    (G.induce cut.side).Connected ∧
      (G.induce (fun vertex => ¬ cut.side vertex)).Connected :=
  ⟨induce_side_connected_of_card_eq hconnected hcyclic cut hcard,
    induce_complement_connected_of_card_eq hconnected hcyclic cut hcard⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Exact cyclic four-edge cuts have connected induced sides once cyclic
four-edge-connectivity is available. -/
theorem induce_both_sides_connected_of_card_eq_four
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    (G.induce cut.side).Connected ∧
      (G.induce (fun vertex => ¬ cut.side vertex)).Connected :=
  induce_both_sides_connected_of_card_eq hconnected hcyclic cut hcard

end

end GoertzelV24CyclicExactCutConnectedSides

end Mettapedia.GraphTheory.FourColor
