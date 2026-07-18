import Mettapedia.GraphTheory.FourColor.GoertzelV24FourDefectBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalCyclicThreeEdgeConnected

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24DeletedEdgeTrail

namespace GoertzelV24FourEdgeCutBoundaryToggle

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

omit [Fintype V] [DecidableRel G.Adj] in
/-- Removing one selected vertex toggles the crossing status of exactly the
edges incident with that vertex. -/
theorem edgeCrosses_remove_side_vertex_iff
    (side : V → Prop) (vertex : V) (hvertex : side vertex)
    (edge : G.edgeSet) :
    EdgeCrossesVertexSide G (fun point ↦ side point ∧ point ≠ vertex) edge ↔
      (EdgeCrossesVertexSide G side edge ∧
          vertex ∉ (edge.1 : Sym2 V)) ∨
        (¬ EdgeCrossesVertexSide G side edge ∧
          vertex ∈ (edge.1 : Sym2 V)) := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      have hne : left ≠ right := by
        exact (SimpleGraph.mem_edgeSet G).1 hedge |>.ne
      by_cases hleftVertex : left = vertex <;>
        by_cases hrightVertex : right = vertex <;>
        by_cases hleftSide : side left <;>
        by_cases hrightSide : side right
      all_goals
        simp_all [EdgeCrossesVertexSide, Sym2.mem_iff, ne_comm]

/-- A cubic side-cycle cannot pass through a vertex already incident with
two distinct crossing edges: the two cycle edges would give four distinct
edges at a cubic vertex. -/
theorem cycle_avoids_side_vertex_of_two_crossing_incident
    (side : V → Prop) (vertex : V) (hvertex : side vertex)
    (hcubic : (incidentEdgeFinset G vertex).card = 3)
    {first second : G.edgeSet}
    (hfirstSecond : first ≠ second)
    (hfirstIncident : first ∈ incidentEdgeFinset G vertex)
    (hsecondIncident : second ∈ incidentEdgeFinset G vertex)
    (hfirstCross : EdgeCrossesVertexSide G side first)
    (hsecondCross : EdgeCrossesVertexSide G side second)
    (cycle : G.Walk root root) (hcycle : cycle.IsCycle)
    (hcycleSide : ∀ point, point ∈ cycle.support → side point) :
    vertex ∉ cycle.support := by
  intro hvertexSupport
  let rotated := cycle.rotate vertex hvertexSupport
  have hrotatedCycle : rotated.IsCycle := hcycle.rotate hvertexSupport
  have hrotatedNotNil : ¬ rotated.Nil := hrotatedCycle.not_nil
  have hsndSide : side rotated.snd := by
    apply hcycleSide rotated.snd
    apply (cycle.mem_support_rotate_iff vertex hvertexSupport).1
    exact rotated.getVert_mem_support 1
  have hpenultimateSide : side rotated.penultimate := by
    apply hcycleSide rotated.penultimate
    apply (cycle.mem_support_rotate_iff vertex hvertexSupport).1
    exact rotated.getVert_mem_support (rotated.length - 1)
  have hsndAdj : G.Adj vertex rotated.snd :=
    rotated.adj_snd hrotatedNotNil
  have hpenultimateAdj : G.Adj vertex rotated.penultimate :=
    (rotated.adj_penultimate hrotatedNotNil).symm
  let firstCycleEdge : G.edgeSet :=
    ⟨s(vertex, rotated.snd), hsndAdj⟩
  let secondCycleEdge : G.edgeSet :=
    ⟨s(vertex, rotated.penultimate), hpenultimateAdj⟩
  have hfirstCycleIncident :
      firstCycleEdge ∈ incidentEdgeFinset G vertex := by
    simp [firstCycleEdge, incidentEdgeFinset]
  have hsecondCycleIncident :
      secondCycleEdge ∈ incidentEdgeFinset G vertex := by
    simp [secondCycleEdge, incidentEdgeFinset]
  have hfirstCycleNotCross :
      ¬ EdgeCrossesVertexSide G side firstCycleEdge := by
    rw [not_edgeCrossesVertexSide_iff_forall_side_iff]
    intro left right hleft hright
    simp only [firstCycleEdge, Sym2.mem_iff] at hleft hright
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl <;>
      simp [hvertex, hsndSide]
  have hsecondCycleNotCross :
      ¬ EdgeCrossesVertexSide G side secondCycleEdge := by
    rw [not_edgeCrossesVertexSide_iff_forall_side_iff]
    intro left right hleft hright
    simp only [secondCycleEdge, Sym2.mem_iff] at hleft hright
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl <;>
      simp [hvertex, hpenultimateSide]
  have hfirstNeFirstCycle : first ≠ firstCycleEdge := by
    intro heq
    apply hfirstCycleNotCross
    simpa [heq] using hfirstCross
  have hfirstNeSecondCycle : first ≠ secondCycleEdge := by
    intro heq
    apply hsecondCycleNotCross
    simpa [heq] using hfirstCross
  have hsecondNeFirstCycle : second ≠ firstCycleEdge := by
    intro heq
    apply hfirstCycleNotCross
    simpa [heq] using hsecondCross
  have hsecondNeSecondCycle : second ≠ secondCycleEdge := by
    intro heq
    apply hsecondCycleNotCross
    simpa [heq] using hsecondCross
  have hcycleEdgesNe : firstCycleEdge ≠ secondCycleEdge := by
    intro heq
    have hvalues := congrArg Subtype.val heq
    have hsndNeVertex : rotated.snd ≠ vertex := hsndAdj.ne.symm
    have hpenultimateNeVertex : rotated.penultimate ≠ vertex :=
      hpenultimateAdj.ne.symm
    have hsndEq : rotated.snd = rotated.penultimate := by
      simpa [firstCycleEdge, secondCycleEdge, Sym2.eq_iff,
        hsndNeVertex, hpenultimateNeVertex] using hvalues
    exact hrotatedCycle.snd_ne_penultimate hsndEq
  have hfourSubset :
      ({first, second, firstCycleEdge, secondCycleEdge} :
          Finset G.edgeSet) ⊆ incidentEdgeFinset G vertex := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl | rfl
    · exact hfirstIncident
    · exact hsecondIncident
    · exact hfirstCycleIncident
    · exact hsecondCycleIncident
  have hfourCard :
      ({first, second, firstCycleEdge, secondCycleEdge} :
          Finset G.edgeSet).card = 4 := by
    simp [hfirstSecond, hfirstNeFirstCycle, hfirstNeSecondCycle,
      hsecondNeFirstCycle, hsecondNeSecondCycle, hcycleEdgesNe,
      ]
  have hcardLe := Finset.card_le_card hfourSubset
  omega

/-- The symmetric difference of a side boundary with one incident vertex
star. This is the exact edge boundary after removing that vertex. -/
def vertexSideBoundaryToggleEdges
    (cut : SmallCyclicEdgeCut G) (vertex : V) : Finset G.edgeSet :=
  (cut.edgeCut \ incidentEdgeFinset G vertex) ∪
    (incidentEdgeFinset G vertex \ cut.edgeCut)

theorem vertexSideBoundaryToggleEdges_mem_iff
    (cut : SmallCyclicEdgeCut G) (vertex : V) (hvertex : cut.side vertex)
    (edge : G.edgeSet) :
    edge ∈ vertexSideBoundaryToggleEdges cut vertex ↔
      EdgeCrossesVertexSide G
        (fun point ↦ cut.side point ∧ point ≠ vertex) edge := by
  rw [edgeCrosses_remove_side_vertex_iff cut.side vertex hvertex edge]
  rw [← cut.hcut_eq edge]
  simp only [vertexSideBoundaryToggleEdges, Finset.mem_union,
    Finset.mem_sdiff]
  simp [incidentEdgeFinset]
  tauto

/-- Removing a side vertex carrying two cut edges preserves the side-cycle,
because the cycle avoids that vertex. -/
theorem hasCycleOnSide_remove_vertex_of_two_crossing_incident
    (hcubic : ∀ point, (incidentEdgeFinset G point).card = 3)
    (cut : SmallCyclicEdgeCut G) (vertex : V) (hvertex : cut.side vertex)
    {first second : G.edgeSet}
    (hfirstSecond : first ≠ second)
    (hfirstIncident : first ∈ incidentEdgeFinset G vertex)
    (hsecondIncident : second ∈ incidentEdgeFinset G vertex)
    (hfirstCut : first ∈ cut.edgeCut)
    (hsecondCut : second ∈ cut.edgeCut) :
    HasCycleOnSide G (fun point ↦ cut.side point ∧ point ≠ vertex) := by
  rcases cut.hinside_cycle with
    ⟨root, hroot, cycle, hcycle, hcycleSide⟩
  have havoid := cycle_avoids_side_vertex_of_two_crossing_incident
    cut.side vertex hvertex (hcubic vertex) hfirstSecond
    hfirstIncident hsecondIncident
    ((cut.hcut_eq first).1 hfirstCut)
    ((cut.hcut_eq second).1 hsecondCut)
    cycle hcycle hcycleSide
  refine ⟨root, ⟨hroot, ?_⟩, cycle, hcycle, ?_⟩
  · intro hrootVertex
    apply havoid
    simpa [hrootVertex] using cycle.start_mem_support
  · intro point hpoint
    exact ⟨hcycleSide point hpoint, fun hpointVertex =>
      havoid (hpointVertex ▸ hpoint)⟩

/-- The exact cyclic-cut realization obtained by removing a side vertex
incident with two cut edges. -/
def removeSideVertexRealization
    (hcubic : ∀ point, (incidentEdgeFinset G point).card = 3)
    (cut : SmallCyclicEdgeCut G) (vertex : V) (hvertex : cut.side vertex)
    {first second : G.edgeSet}
    (hfirstSecond : first ≠ second)
    (hfirstIncident : first ∈ incidentEdgeFinset G vertex)
    (hsecondIncident : second ∈ incidentEdgeFinset G vertex)
    (hfirstCut : first ∈ cut.edgeCut)
    (hsecondCut : second ∈ cut.edgeCut) :
    CyclicEdgeCutRealization G
      (vertexSideBoundaryToggleEdges cut vertex) where
  side := fun point ↦ cut.side point ∧ point ≠ vertex
  hcut_eq := vertexSideBoundaryToggleEdges_mem_iff cut vertex hvertex
  hinside_cycle :=
    hasCycleOnSide_remove_vertex_of_two_crossing_incident
      hcubic cut vertex hvertex hfirstSecond hfirstIncident hsecondIncident
      hfirstCut hsecondCut
  houtside_cycle := cut.houtside_cycle.mono (by
    intro point houtside hnewSide
    exact houtside hnewSide.1)

/-- For an exact four-cut at a cubic vertex, toggling a vertex incident with
two cut edges leaves a boundary of cardinality at most three. -/
theorem card_vertexSideBoundaryToggleEdges_le_three
    (hcubic : ∀ point, (incidentEdgeFinset G point).card = 3)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (vertex : V) {first second : G.edgeSet}
    (hfirstSecond : first ≠ second)
    (hfirstIncident : first ∈ incidentEdgeFinset G vertex)
    (hsecondIncident : second ∈ incidentEdgeFinset G vertex)
    (hfirstCut : first ∈ cut.edgeCut)
    (hsecondCut : second ∈ cut.edgeCut) :
    (vertexSideBoundaryToggleEdges cut vertex).card ≤ 3 := by
  let incident := incidentEdgeFinset G vertex
  have hpairSubset : ({first, second} : Finset G.edgeSet) ⊆
      cut.edgeCut ∩ incident := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hfirstCut, hfirstIncident⟩
    · exact Finset.mem_inter.mpr ⟨hsecondCut, hsecondIncident⟩
  have hpairCard : ({first, second} : Finset G.edgeSet).card = 2 := by
    simp [hfirstSecond]
  have hintersectionCard : 2 ≤ (cut.edgeCut ∩ incident).card := by
    have := Finset.card_le_card hpairSubset
    omega
  have hfirstPartition :=
    Finset.card_sdiff_add_card_inter cut.edgeCut incident
  have hsecondPartition :=
    Finset.card_sdiff_add_card_inter incident cut.edgeCut
  have hintersections :
      (incident ∩ cut.edgeCut).card = (cut.edgeCut ∩ incident).card := by
    rw [Finset.inter_comm]
  have hdisjoint : Disjoint (cut.edgeCut \ incident)
      (incident \ cut.edgeCut) := by
    rw [Finset.disjoint_left]
    intro edge hfirst hsecond
    exact (Finset.mem_sdiff.mp hfirst).2
      (Finset.mem_sdiff.mp hsecond).1
  have hunionCard :
      (vertexSideBoundaryToggleEdges cut vertex).card =
        (cut.edgeCut \ incident).card +
          (incident \ cut.edgeCut).card := by
    exact Finset.card_union_of_disjoint hdisjoint
  have hincidentCard : incident.card = 3 := hcubic vertex
  omega

/-- In a cubic graph of cyclic edge-connectivity at least four, the four
edges of an exact cyclic four-cut have distinct endpoints on either chosen
side. Two shared incidences would produce a cyclic cut of size at most
three by removing their common side vertex. -/
theorem no_two_cut_edges_share_side_vertex
    (hcubic : ∀ point, (incidentEdgeFinset G point).card = 3)
    (hcyclic : CyclicEdgeConnectivityAtLeast G 4)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (vertex : V) (hvertex : cut.side vertex)
    {first second : G.edgeSet}
    (hfirstSecond : first ≠ second)
    (hfirstIncident : first ∈ incidentEdgeFinset G vertex)
    (hsecondIncident : second ∈ incidentEdgeFinset G vertex)
    (hfirstCut : first ∈ cut.edgeCut)
    (hsecondCut : second ∈ cut.edgeCut) : False := by
  let realization := removeSideVertexRealization hcubic cut vertex hvertex
    hfirstSecond hfirstIncident hsecondIncident hfirstCut hsecondCut
  have htoggleCard := card_vertexSideBoundaryToggleEdges_le_three
    hcubic cut hcard vertex hfirstSecond hfirstIncident hsecondIncident
      hfirstCut hsecondCut
  let smallerCut := realization.toSmallCyclicEdgeCut (by omega)
  have hminimum : 4 ≤ smallerCut.edgeCut.card := hcyclic smallerCut
  change 4 ≤ (vertexSideBoundaryToggleEdges cut vertex).card at hminimum
  omega

end

end GoertzelV24FourEdgeCutBoundaryToggle

end Mettapedia.GraphTheory.FourColor
