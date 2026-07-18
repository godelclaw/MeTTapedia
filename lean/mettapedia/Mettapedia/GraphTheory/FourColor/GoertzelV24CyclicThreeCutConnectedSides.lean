import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalCyclicThreeEdgeConnected

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CyclicThreeCutConnectedSides

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The vertices reachable from a root without leaving a fixed vertex side. -/
def inducedReachableSide (G : SimpleGraph V) (side : V → Prop)
    (root : V) (hroot : side root) (vertex : V) : Prop :=
  ∃ hvertex : side vertex,
    (G.induce side).Reachable
      ⟨root, hroot⟩ ⟨vertex, hvertex⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem inducedReachableSide_root
    (side : V → Prop) (root : V) (hroot : side root) :
    inducedReachableSide G side root hroot root := by
  exact ⟨hroot, .rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem inducedReachableSide_mem
    {side : V → Prop} {root : V} {hroot : side root} {vertex : V}
    (hvertex : inducedReachableSide G side root hroot vertex) :
    side vertex :=
  hvertex.choose

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A cycle based at the root remains a cycle on the root's induced-side
reachable component. -/
theorem hasCycleOnSide_inducedReachableSide
    (side : V → Prop) (root : V) (hroot : side root)
    (walk : G.Walk root root) (hcycle : walk.IsCycle)
    (hsupport : ∀ vertex, vertex ∈ walk.support → side vertex) :
    HasCycleOnSide G (inducedReachableSide G side root hroot) := by
  refine ⟨root, inducedReachableSide_root side root hroot,
    walk, hcycle, ?_⟩
  intro vertex hvertex
  refine ⟨hsupport vertex hvertex, ?_⟩
  have hsupportReachable :
      (G.induce {point | point ∈ walk.support}).Reachable
        ⟨root, walk.start_mem_support⟩ ⟨vertex, hvertex⟩ :=
    walk.connected_induce_support.preconnected _ _
  let inclusion :=
    G.induceHomOfLE (fun point hpoint => hsupport point hpoint)
  have hmapped := hsupportReachable.map inclusion.toHom
  convert hmapped using 1 <;> apply Subtype.ext <;> rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Any edge leaving an induced-side reachable component already crosses the
original side. -/
theorem edgeCrossesVertexSide_of_inducedReachableSide
    (side : V → Prop) (root : V) (hroot : side root)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (inducedReachableSide G side root hroot) edge) :
    EdgeCrossesVertexSide G side edge := by
  rcases hcross with
    ⟨inner, outer, hinnerEdge, houterEdge, hinner, houter⟩
  have hinnerSide : side inner := inducedReachableSide_mem hinner
  by_cases houterSide : side outer
  · have hne : inner ≠ outer := by
      intro heq
      exact houter (heq ▸ hinner)
    have hedge : (edge : Sym2 V) = s(inner, outer) :=
      sym2_eq_mk_of_mem_of_mem_of_ne hinnerEdge houterEdge hne
    have hadj : G.Adj inner outer :=
      (SimpleGraph.mem_edgeSet G).1 (by simpa [hedge] using edge.2)
    have hinducedAdj :
        (G.induce side).Adj
          ⟨inner, hinnerSide⟩ ⟨outer, houterSide⟩ :=
      hadj
    apply False.elim
    apply houter
    exact ⟨houterSide, hinner.choose_spec.trans hinducedAdj.reachable⟩
  · exact ⟨inner, outer, hinnerEdge, houterEdge,
      hinnerSide, houterSide⟩

/-- The exact edge cut of the root's reachable side component. -/
def inducedReachableCyclicCut
    (cut : SmallCyclicEdgeCut G)
    (root : V) (hroot : cut.side root)
    (walk : G.Walk root root) (hcycle : walk.IsCycle)
    (hsupport : ∀ vertex, vertex ∈ walk.support → cut.side vertex) :
    SmallCyclicEdgeCut G := by
  classical
  exact
    { edgeCut := cut.edgeCut.filter fun edge =>
        EdgeCrossesVertexSide G
          (inducedReachableSide G cut.side root hroot) edge
      side := inducedReachableSide G cut.side root hroot
      hcut_eq := by
        intro edge
        simp only [Finset.mem_filter]
        constructor
        · exact fun hedge => hedge.2
        · intro hcross
          exact ⟨(cut.hcut_eq edge).2
              (edgeCrossesVertexSide_of_inducedReachableSide
                cut.side root hroot edge hcross),
            hcross⟩
      hcard_le_four := by
        exact le_trans (Finset.card_filter_le _ _ ) cut.hcard_le_four
      hinside_cycle :=
        hasCycleOnSide_inducedReachableSide cut.side root hroot
          walk hcycle hsupport
      houtside_cycle := by
        exact HasCycleOnSide.mono
          (fun vertex houtside hcomponent =>
            houtside (inducedReachableSide_mem hcomponent))
          cut.houtside_cycle }

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem inducedReachableCyclicCut_edgeCut_subset
    (cut : SmallCyclicEdgeCut G)
    (root : V) (hroot : cut.side root)
    (walk : G.Walk root root) (hcycle : walk.IsCycle)
    (hsupport : ∀ vertex, vertex ∈ walk.support → cut.side vertex) :
    (inducedReachableCyclicCut cut root hroot walk hcycle hsupport).edgeCut ⊆
      cut.edgeCut := by
  classical
  intro edge hedge
  change edge ∈ cut.edgeCut.filter (fun edge =>
    EdgeCrossesVertexSide G
      (inducedReachableSide G cut.side root hroot) edge) at hedge
  exact (Finset.mem_filter.mp hedge).1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In a connected graph with cyclic edge-connectivity at least three, both
sides of an exact cyclic three-edge cut are induced connected subgraphs. -/
theorem induce_side_connected_of_card_eq_three
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 3)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 3) :
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
    have hcomponentCard : 3 ≤ componentCut.edgeCut.card := hcyclic componentCut
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
    have hcrossComponent : EdgeCrossesVertexSide G component edge := by
      exact (componentCut.hcut_eq edge).1 hedgeComponentCut
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
theorem induce_complement_connected_of_card_eq_three
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 3)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 3) :
    (G.induce (fun vertex => ¬ cut.side vertex)).Connected := by
  change (G.induce cut.compl.side).Connected
  exact induce_side_connected_of_card_eq_three
    hconnected hcyclic cut.compl hcard

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem induce_both_sides_connected_of_card_eq_three
    (hconnected : G.Connected)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 3)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 3) :
    (G.induce cut.side).Connected ∧
      (G.induce (fun vertex => ¬ cut.side vertex)).Connected :=
  ⟨induce_side_connected_of_card_eq_three hconnected hcyclic cut hcard,
    induce_complement_connected_of_card_eq_three
      hconnected hcyclic cut hcard⟩

end


end GoertzelV24CyclicThreeCutConnectedSides

end Mettapedia.GraphTheory.FourColor
