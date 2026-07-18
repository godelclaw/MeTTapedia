import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutBoundaryToggle
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutMinimality

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24DeletedEdgeTrail
open GoertzelV24FourDefectBoundary
open GoertzelV24FourEdgeCutBoundaryToggle
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24ThreeEdgeCutMinimality

namespace GoertzelV24FourEdgeCutBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Enumerate the four edges of an exact cyclic cut. -/
def cyclicCutCrossingOfCardFour
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    Fin 4 → G.edgeSet :=
  fun step ↦
    ((Fintype.equivFinOfCardEq (by simpa using hcard) :
      cut.edgeCut ≃ Fin 4).symm step).1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cyclicCutCrossingOfCardFour_injective
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    Function.Injective (cyclicCutCrossingOfCardFour cut hcard) := by
  intro left right heq
  apply (Fintype.equivFinOfCardEq (by simpa using hcard) :
    cut.edgeCut ≃ Fin 4).symm.injective
  exact Subtype.ext heq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cyclicCutCrossingOfCardFour_mem
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) :
    cyclicCutCrossingOfCardFour cut hcard step ∈ cut.edgeCut :=
  ((Fintype.equivFinOfCardEq (by simpa using hcard) :
    cut.edgeCut ≃ Fin 4).symm step).2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem orderedCut_cyclicCutCrossingOfCardFour
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    orderedCut (cyclicCutCrossingOfCardFour cut hcard) = cut.edgeCut := by
  ext edge
  constructor
  · intro hedge
    rcases Finset.mem_image.mp hedge with ⟨step, _hstep, rfl⟩
    exact cyclicCutCrossingOfCardFour_mem cut hcard step
  · intro hedge
    let edgeInCut : cut.edgeCut := ⟨edge, hedge⟩
    let step := (Fintype.equivFinOfCardEq (by simpa using hcard) :
      cut.edgeCut ≃ Fin 4) edgeInCut
    apply Finset.mem_image.mpr
    refine ⟨step, Finset.mem_univ step, ?_⟩
    change ((Fintype.equivFinOfCardEq (by simpa using hcard) :
      cut.edgeCut ≃ Fin 4).symm step).1 = edge
    exact congrArg Subtype.val
      ((Fintype.equivFinOfCardEq (by simpa using hcard) :
        cut.edgeCut ≃ Fin 4).symm_apply_apply edgeInCut)

/-- A chosen endpoint lying on the selected side of a crossing edge. -/
def sideEndpointOfCrossing
    (side : V → Prop) (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G side edge) : V :=
  Classical.choose hcross

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem sideEndpointOfCrossing_mem
    (side : V → Prop) (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G side edge) :
    sideEndpointOfCrossing side edge hcross ∈ (edge.1 : Sym2 V) :=
  (Classical.choose_spec (Classical.choose_spec hcross)).1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem sideEndpointOfCrossing_side
    (side : V → Prop) (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G side edge) :
    side (sideEndpointOfCrossing side edge hcross) :=
  (Classical.choose_spec (Classical.choose_spec hcross)).2.2.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A crossing edge has exactly one endpoint on either chosen side. -/
theorem side_endpoint_unique_of_crossing
    (side : V → Prop) (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G side edge)
    {first second : V}
    (hfirstMem : first ∈ (edge.1 : Sym2 V))
    (hsecondMem : second ∈ (edge.1 : Sym2 V))
    (hfirstSide : side first) (hsecondSide : side second) :
    first = second := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hopposite : ¬ (side left ↔ side right) :=
        not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq rfl hcross
      simp only [Sym2.mem_iff] at hfirstMem hsecondMem
      rcases hfirstMem with rfl | rfl <;>
        rcases hsecondMem with rfl | rfl
      · rfl
      · exact (hopposite ⟨fun _ ↦ hsecondSide,
          fun _ ↦ hfirstSide⟩).elim
      · exact (hopposite ⟨fun _ ↦ hfirstSide,
          fun _ ↦ hsecondSide⟩).elim
      · rfl

/-- The endpoint on the selected side of one enumerated four-cut edge. -/
def cyclicCutSideEndpoint
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) : V :=
  sideEndpointOfCrossing cut.side
    (cyclicCutCrossingOfCardFour cut hcard step)
    ((cut.hcut_eq _).1
      (cyclicCutCrossingOfCardFour_mem cut hcard step))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cyclicCutSideEndpoint_mem_edge
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) :
    cyclicCutSideEndpoint cut hcard step ∈
      ((cyclicCutCrossingOfCardFour cut hcard step).1 : Sym2 V) := by
  apply sideEndpointOfCrossing_mem

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem cyclicCutSideEndpoint_side
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) :
    cut.side (cyclicCutSideEndpoint cut hcard step) := by
  apply sideEndpointOfCrossing_side

/-- The endpoint opposite the selected-side endpoint of one enumerated
four-cut edge. -/
def cyclicCutOutsideEndpoint
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) : V :=
  Sym2.Mem.other' (cyclicCutSideEndpoint_mem_edge cut hcard step)

omit [Fintype V] [DecidableRel G.Adj] in
theorem cyclicCutCrossingOfCardFour_val
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) :
    (cyclicCutCrossingOfCardFour cut hcard step).1 =
      s(cyclicCutSideEndpoint cut hcard step,
        cyclicCutOutsideEndpoint cut hcard step) := by
  exact (Sym2.other_spec'
    (cyclicCutSideEndpoint_mem_edge cut hcard step)).symm

omit [Fintype V] [DecidableRel G.Adj] in
theorem cyclicCutOutsideEndpoint_not_side
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) :
    ¬ cut.side (cyclicCutOutsideEndpoint cut hcard step) := by
  have hcross : EdgeCrossesVertexSide G cut.side
      (cyclicCutCrossingOfCardFour cut hcard step) :=
    (cut.hcut_eq _).1 (cyclicCutCrossingOfCardFour_mem cut hcard step)
  have hopposite : ¬
      (cut.side (cyclicCutSideEndpoint cut hcard step) ↔
        cut.side (cyclicCutOutsideEndpoint cut hcard step)) :=
    not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
      (cyclicCutCrossingOfCardFour_val cut hcard step) hcross
  intro houtside
  exact hopposite ⟨fun _ ↦ houtside,
    fun _ ↦ cyclicCutSideEndpoint_side cut hcard step⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem cyclicCutSideEndpoint_adj_outsideEndpoint
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) :
    G.Adj (cyclicCutSideEndpoint cut hcard step)
      (cyclicCutOutsideEndpoint cut hcard step) := by
  apply (SimpleGraph.mem_edgeSet G).1
  rw [← cyclicCutCrossingOfCardFour_val cut hcard step]
  exact (cyclicCutCrossingOfCardFour cut hcard step).2

/-- Vertices on the selected side of a cyclic cut. -/
abbrev CyclicCutSideVertex (cut : SmallCyclicEdgeCut G) :=
  {vertex : V // cut.side vertex}

/-- The graph induced by the selected side of a cyclic cut. -/
abbrev CyclicCutSideGraph (cut : SmallCyclicEdgeCut G) :
    SimpleGraph (CyclicCutSideVertex cut) :=
  G.induce {vertex | cut.side vertex}

/-- An enumerated four-cut endpoint as a vertex of its induced side. -/
def cyclicCutSidePort
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) : CyclicCutSideVertex cut :=
  ⟨cyclicCutSideEndpoint cut hcard step,
    cyclicCutSideEndpoint_side cut hcard step⟩

/-- Inclusion of selected-side vertices into the ambient carrier. -/
def cyclicCutSideEmbedding (cut : SmallCyclicEdgeCut G) :
    CyclicCutSideVertex cut ↪ V :=
  Function.Embedding.subtype
    (fun vertex : V ↦ vertex ∈ {point | cut.side point})

/-- The computed neighbor finset does not depend on which finite-type
presentation of the same finite neighbor set is in scope. -/
theorem neighborFinset_instance_independent
    {W : Type*} (H : SimpleGraph W) (vertex : W)
    (first second : Fintype (H.neighborSet vertex)) :
    @SimpleGraph.neighborFinset W H vertex first =
      @SimpleGraph.neighborFinset W H vertex second := by
  ext other
  simp

/-- Consequently graph degree is independent of the finite-type
presentation used to compute it. -/
theorem degree_instance_independent
    {W : Type*} (H : SimpleGraph W) (vertex : W)
    (first second : Fintype (H.neighborSet vertex)) :
    @SimpleGraph.degree W H vertex first =
      @SimpleGraph.degree W H vertex second := by
  exact congrArg Finset.card
    (neighborFinset_instance_independent H vertex first second)

omit [DecidableRel G.Adj] in
/-- Neighbor finsets in the induced side are exactly the ambient neighbors
that remain on the selected side. -/
theorem map_neighborFinset_cyclicCutSideGraph
    (cut : SmallCyclicEdgeCut G) (vertex : CyclicCutSideVertex cut) :
    (SimpleGraph.neighborFinset (G := CyclicCutSideGraph cut) vertex).map
        (cyclicCutSideEmbedding cut) =
      G.neighborFinset vertex.1 ∩ cyclicCutVertexSide cut := by
  classical
  ext point
  simp [cyclicCutSideEmbedding, mem_cyclicCutVertexSide_iff]
  constructor
  · rintro ⟨hside, hadj⟩
    exact ⟨hadj, hside⟩
  · rintro ⟨hadj, hside⟩
    exact ⟨hside, hadj⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every edge from a selected-side vertex to an outside neighbor is one
of the four enumerated cut edges. -/
theorem exists_cyclicCutCrossingOfCardFour_eq_of_adj_not_side
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (vertex other : V) (hvertex : cut.side vertex)
    (hadj : G.Adj vertex other) (hother : ¬ cut.side other) :
    ∃ step : Fin 4,
      cyclicCutCrossingOfCardFour cut hcard step =
        (⟨s(vertex, other), hadj⟩ : G.edgeSet) := by
  let edge : G.edgeSet := ⟨s(vertex, other), hadj⟩
  have hcross : EdgeCrossesVertexSide G cut.side edge :=
    ⟨vertex, other, by simp [edge], by simp [edge], hvertex, hother⟩
  have hedgeCut : edge ∈ cut.edgeCut := (cut.hcut_eq edge).2 hcross
  rw [← orderedCut_cyclicCutCrossingOfCardFour cut hcard] at hedgeCut
  rcases Finset.mem_image.mp hedgeCut with ⟨step, _hstep, hedge⟩
  exact ⟨step, hedge⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The selected endpoint of the enumerated cut edge determined by an
outside neighbor is the original selected-side vertex. -/
theorem cyclicCutSideEndpoint_eq_of_crossing_eq_adj
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (vertex other : V) (hvertex : cut.side vertex)
    (hadj : G.Adj vertex other) (step : Fin 4)
    (hedge : cyclicCutCrossingOfCardFour cut hcard step =
      (⟨s(vertex, other), hadj⟩ : G.edgeSet)) :
    cyclicCutSideEndpoint cut hcard step = vertex := by
  apply side_endpoint_unique_of_crossing cut.side
    (cyclicCutCrossingOfCardFour cut hcard step)
    ((cut.hcut_eq _).1 (cyclicCutCrossingOfCardFour_mem cut hcard step))
  · exact cyclicCutSideEndpoint_mem_edge cut hcard step
  · simp [hedge]
  · exact cyclicCutSideEndpoint_side cut hcard step
  · exact hvertex

/-- Cyclic four-edge-connectivity makes the four selected-side ports
pairwise distinct. -/
theorem cyclicCutSidePort_injective
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    Function.Injective (cyclicCutSidePort cut hcard) := by
  intro first second heq
  by_contra hne
  have hedgeNe : cyclicCutCrossingOfCardFour cut hcard first ≠
      cyclicCutCrossingOfCardFour cut hcard second :=
    fun hedge ↦ hne
      (cyclicCutCrossingOfCardFour_injective cut hcard hedge)
  have hendpointEq : cyclicCutSideEndpoint cut hcard first =
      cyclicCutSideEndpoint cut hcard second :=
    congrArg Subtype.val heq
  exact no_two_cut_edges_share_side_vertex hcubic hcyclic cut hcard
    (cyclicCutSideEndpoint cut hcard first)
    (cyclicCutSideEndpoint_side cut hcard first) hedgeNe
    (by simpa [incidentEdgeFinset] using
      cyclicCutSideEndpoint_mem_edge cut hcard first)
    (by simpa [hendpointEq, incidentEdgeFinset] using
      cyclicCutSideEndpoint_mem_edge cut hcard second)
    (cyclicCutCrossingOfCardFour_mem cut hcard first)
    (cyclicCutCrossingOfCardFour_mem cut hcard second)

/-- Any outside neighbor of a four-cut port is the opposite endpoint of
that port's enumerated cut edge. -/
theorem outside_neighbor_eq_cyclicCutOutsideEndpoint
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) (other : V)
    (hadj : G.Adj (cyclicCutSideEndpoint cut hcard step) other)
    (hother : ¬ cut.side other) :
    other = cyclicCutOutsideEndpoint cut hcard step := by
  rcases exists_cyclicCutCrossingOfCardFour_eq_of_adj_not_side
      cut hcard (cyclicCutSideEndpoint cut hcard step) other
      (cyclicCutSideEndpoint_side cut hcard step) hadj hother with
    ⟨otherStep, hedge⟩
  have hendpoint : cyclicCutSideEndpoint cut hcard otherStep =
      cyclicCutSideEndpoint cut hcard step :=
    cyclicCutSideEndpoint_eq_of_crossing_eq_adj cut hcard
      (cyclicCutSideEndpoint cut hcard step) other
      (cyclicCutSideEndpoint_side cut hcard step) hadj otherStep hedge
  have hstep : otherStep = step :=
    cyclicCutSidePort_injective hcubic hcyclic cut hcard
      (Subtype.ext hendpoint)
  subst otherStep
  have hpairs :
      s(cyclicCutSideEndpoint cut hcard step, other) =
        s(cyclicCutSideEndpoint cut hcard step,
          cyclicCutOutsideEndpoint cut hcard step) :=
    (congrArg Subtype.val hedge).symm.trans
      (cyclicCutCrossingOfCardFour_val cut hcard step)
  rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
  · exact hstraight.2
  · exact (cyclicCutOutsideEndpoint_not_side cut hcard step
      (hswapped.1 ▸ cyclicCutSideEndpoint_side cut hcard step)).elim

/-- Ambient neighbors outside the selected side. -/
def cyclicCutOutsideNeighborFinset
    (cut : SmallCyclicEdgeCut G) (vertex : V) : Finset V :=
  G.neighborFinset vertex \ cyclicCutVertexSide cut

/-- At each four-cut port there is exactly one ambient neighbor outside the
selected side. -/
theorem cyclicCutOutsideNeighborFinset_port
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) :
    cyclicCutOutsideNeighborFinset cut
        (cyclicCutSideEndpoint cut hcard step) =
      {cyclicCutOutsideEndpoint cut hcard step} := by
  ext other
  constructor
  · intro hmem
    have hdata := Finset.mem_sdiff.mp hmem
    have hadj : G.Adj (cyclicCutSideEndpoint cut hcard step) other := by
      simpa using hdata.1
    have hother : ¬ cut.side other := by
      intro hside
      exact hdata.2
        ((mem_cyclicCutVertexSide_iff cut other).2 hside)
    exact Finset.mem_singleton.mpr
      (outside_neighbor_eq_cyclicCutOutsideEndpoint
        hcubic hcyclic cut hcard step other hadj hother)
  · intro hmem
    have heq := Finset.mem_singleton.mp hmem
    subst other
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · simpa using
        cyclicCutSideEndpoint_adj_outsideEndpoint cut hcard step
    · intro hside
      exact cyclicCutOutsideEndpoint_not_side cut hcard step
        ((mem_cyclicCutVertexSide_iff cut _).1 hside)

/-- Each selected-side port has degree two in the graph induced by that
side. -/
theorem cyclicCutSidePort_incidentEdgeFinset_card_eq_two
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (step : Fin 4) :
    (incidentEdgeFinset (CyclicCutSideGraph cut)
      (cyclicCutSidePort cut hcard step)).card = 2 := by
  letI : Fintype
      (G.neighborSet (cyclicCutSideEndpoint cut hcard step)) :=
    GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype _
  letI : Fintype
      ((CyclicCutSideGraph cut).neighborSet
        (cyclicCutSidePort cut hcard step)) :=
    GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype _
  have hambient :
      (G.neighborFinset (cyclicCutSideEndpoint cut hcard step)).card = 3 := by
    calc
      _ = G.degree (cyclicCutSideEndpoint cut hcard step) :=
        by
          convert SimpleGraph.card_neighborFinset_eq_degree _ _ using 1
      _ = (incidentEdgeFinset G
          (cyclicCutSideEndpoint cut hcard step)).card := by
        convert (incidentEdgeFinset_card_eq_degree _).symm using 1
        apply degree_instance_independent
      _ = 3 := hcubic _
  have houtside :
      (cyclicCutOutsideNeighborFinset cut
        (cyclicCutSideEndpoint cut hcard step)).card = 1 := by
    rw [cyclicCutOutsideNeighborFinset_port
      hcubic hcyclic cut hcard step]
    simp
  have hpartition := Finset.card_sdiff_add_card_inter
    (G.neighborFinset (cyclicCutSideEndpoint cut hcard step))
    (cyclicCutVertexSide cut)
  calc
    (incidentEdgeFinset (CyclicCutSideGraph cut)
        (cyclicCutSidePort cut hcard step)).card =
        (CyclicCutSideGraph cut).degree
          (cyclicCutSidePort cut hcard step) :=
      by
        convert incidentEdgeFinset_card_eq_degree _ using 1
        apply degree_instance_independent
    _ = (SimpleGraph.neighborFinset
        (G := CyclicCutSideGraph cut)
        (cyclicCutSidePort cut hcard step)).card :=
      (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ = ((SimpleGraph.neighborFinset
          (G := CyclicCutSideGraph cut)
          (cyclicCutSidePort cut hcard step)).map
            (cyclicCutSideEmbedding cut)).card := by simp
    _ = (G.neighborFinset (cyclicCutSideEndpoint cut hcard step) ∩
        cyclicCutVertexSide cut).card := by
      have hmapped := congrArg Finset.card
        (map_neighborFinset_cyclicCutSideGraph cut
          (cyclicCutSidePort cut hcard step))
      convert hmapped using 1
      change (G.neighborFinset (cyclicCutSideEndpoint cut hcard step) ∩
        cyclicCutVertexSide cut).card =
          (G.neighborFinset (cyclicCutSideEndpoint cut hcard step) ∩
            cyclicCutVertexSide cut).card
      rfl
    _ = 2 := by
      change (G.neighborFinset (cyclicCutSideEndpoint cut hcard step) \
        cyclicCutVertexSide cut).card = 1 at houtside
      omega

omit [DecidableRel G.Adj] in
/-- A selected-side vertex not among the four ports has no ambient neighbor
outside that side. -/
theorem cyclicCutOutsideNeighborFinset_nonport_eq_empty
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (vertex : CyclicCutSideVertex cut)
    (hvertex : ∀ step, vertex ≠ cyclicCutSidePort cut hcard step) :
    cyclicCutOutsideNeighborFinset cut vertex.1 = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  rcases hnonempty with ⟨other, hotherMem⟩
  have hdata := Finset.mem_sdiff.mp hotherMem
  have hadj : G.Adj vertex.1 other := by simpa using hdata.1
  have hother : ¬ cut.side other := by
    intro hside
    exact hdata.2 ((mem_cyclicCutVertexSide_iff cut other).2 hside)
  rcases exists_cyclicCutCrossingOfCardFour_eq_of_adj_not_side
      cut hcard vertex.1 other vertex.2 hadj hother with
    ⟨step, hedge⟩
  have hendpoint := cyclicCutSideEndpoint_eq_of_crossing_eq_adj
    cut hcard vertex.1 other vertex.2 hadj step hedge
  exact hvertex step (Subtype.ext hendpoint.symm)

/-- Every nonport selected-side vertex retains its ambient cubic degree. -/
theorem cyclicCutSide_nonport_incidentEdgeFinset_card_eq_three
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (vertex : CyclicCutSideVertex cut)
    (hvertex : ∀ step, vertex ≠ cyclicCutSidePort cut hcard step) :
    (incidentEdgeFinset (CyclicCutSideGraph cut) vertex).card = 3 := by
  letI : Fintype (G.neighborSet vertex.1) :=
    GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype _
  letI : Fintype ((CyclicCutSideGraph cut).neighborSet vertex) :=
    GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype _
  have hambient : (G.neighborFinset vertex.1).card = 3 := by
    calc
      _ = G.degree vertex.1 := SimpleGraph.card_neighborFinset_eq_degree _ _
      _ = (incidentEdgeFinset G vertex.1).card := by
        convert (incidentEdgeFinset_card_eq_degree _).symm using 1
        apply degree_instance_independent
      _ = 3 := hcubic _
  have houtside :
      (cyclicCutOutsideNeighborFinset cut vertex.1).card = 0 := by
    rw [cyclicCutOutsideNeighborFinset_nonport_eq_empty
      cut hcard vertex hvertex]
    simp
  have hpartition := Finset.card_sdiff_add_card_inter
    (G.neighborFinset vertex.1) (cyclicCutVertexSide cut)
  calc
    (incidentEdgeFinset (CyclicCutSideGraph cut) vertex).card =
        (CyclicCutSideGraph cut).degree vertex :=
      by
        convert incidentEdgeFinset_card_eq_degree _ using 1
        apply degree_instance_independent
    _ = (SimpleGraph.neighborFinset
        (G := CyclicCutSideGraph cut) vertex).card :=
      (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ = ((SimpleGraph.neighborFinset
          (G := CyclicCutSideGraph cut) vertex).map
            (cyclicCutSideEmbedding cut)).card := by simp
    _ = (G.neighborFinset vertex.1 ∩ cyclicCutVertexSide cut).card := by
      rw [map_neighborFinset_cyclicCutSideGraph]
    _ = 3 := by
      change (G.neighborFinset vertex.1 \ cyclicCutVertexSide cut).card = 0
        at houtside
      omega

/-- The ordered degree-two boundary exposed by an exact cyclic four-cut on
its selected side. -/
def cyclicCutSideDegreeTwoBoundaryData
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    DegreeTwoBoundaryData (CyclicCutSideGraph cut) 4 where
  defectVertex := cyclicCutSidePort cut hcard

/-- An exact cyclic four-cut in a cubic, cyclically four-edge-connected
graph exposes a well-formed four-port boundary on either selected side. -/
theorem cyclicCutSideDegreeTwoBoundaryData_wellFormed
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    (cyclicCutSideDegreeTwoBoundaryData cut hcard).WellFormed := by
  exact ⟨cyclicCutSidePort_injective hcubic hcyclic cut hcard,
    cyclicCutSidePort_incidentEdgeFinset_card_eq_two
      hcubic hcyclic cut hcard,
    cyclicCutSide_nonport_incidentEdgeFinset_card_eq_three
      hcubic cut hcard⟩

/-- Both induced sides of an exact cyclic four-cut carry well-formed
four-port degree-two boundaries. -/
theorem cyclicCutBothSidesDegreeTwoBoundaryData_wellFormed
    (hcubic : ∀ vertex, (incidentEdgeFinset G vertex).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) :
    (cyclicCutSideDegreeTwoBoundaryData cut hcard).WellFormed ∧
      (cyclicCutSideDegreeTwoBoundaryData cut.compl
        (by simpa using hcard)).WellFormed := by
  exact ⟨cyclicCutSideDegreeTwoBoundaryData_wellFormed
      hcubic hcyclic cut hcard,
    cyclicCutSideDegreeTwoBoundaryData_wellFormed
      hcubic hcyclic cut.compl (by simpa using hcard)⟩

end

end GoertzelV24FourEdgeCutBoundaryData

end Mettapedia.GraphTheory.FourColor
