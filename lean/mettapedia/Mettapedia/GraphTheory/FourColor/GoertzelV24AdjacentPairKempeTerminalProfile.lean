import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeCutProfile
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open GoertzelV24FourDefectBoundary
open GoertzelV24FramedTrail

namespace GoertzelV24KempeEndpoint

local instance terminalNeighborSetFintype
    {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (vertex : W) :
    Fintype (H.neighborSet vertex) :=
  Subtype.fintype _

/-- In a finite connected graph of maximum degree two, at most two vertices
have subsingleton neighbor sets. -/
theorem terminalVertices_card_le_two
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hconnected : H.Connected)
    (hdegree : ∀ vertex : W, (H.neighborSet vertex).ncard ≤ 2) :
    (Finset.univ.filter fun vertex =>
      (H.neighborSet vertex).Subsingleton).card ≤ 2 := by
  classical
  let terminals := Finset.univ.filter fun vertex =>
    (H.neighborSet vertex).Subsingleton
  have hterminalDegree : ∀ vertex : W,
      (H.neighborSet vertex).Subsingleton → H.degree vertex ≤ 1 := by
    intro vertex hterminal
    rw [← H.card_neighborFinset_eq_degree]
    rw [Finset.card_le_one]
    intro first hfirst second hsecond
    apply hterminal
    · simpa using hfirst
    · simpa using hsecond
  have hpointwise : ∀ vertex : W,
      H.degree vertex +
          (if (H.neighborSet vertex).Subsingleton then 1 else 0) ≤ 2 := by
    intro vertex
    have hdegreeVertex : H.degree vertex ≤ 2 := by
      calc
        H.degree vertex = Fintype.card (H.neighborSet vertex) :=
          (H.card_neighborSet_eq_degree vertex).symm
        _ = (H.neighborSet vertex).ncard :=
          Set.fintypeCard_eq_ncard _
        _ ≤ 2 := hdegree vertex
    by_cases hterminal : (H.neighborSet vertex).Subsingleton
    · simp only [if_pos hterminal]
      exact (Nat.add_le_add_right
        (hterminalDegree vertex hterminal) 1)
    · simp only [if_neg hterminal, add_zero]
      exact hdegreeVertex
  have hsum := Finset.sum_le_sum fun vertex
    (_hvertex : vertex ∈ (Finset.univ : Finset W)) => hpointwise vertex
  have hupper :
      (∑ vertex : W, H.degree vertex) + terminals.card ≤
        2 * Fintype.card W := by
    simpa [terminals, Finset.sum_add_distrib, Nat.mul_comm] using hsum
  have hlower :
      Fintype.card W ≤ H.edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card, ← H.edgeFinset_card] using
      hconnected.card_vert_le_card_edgeSet_add_one
  have hhandshake :
      (∑ vertex : W, H.degree vertex) = 2 * H.edgeFinset.card :=
    by simpa only [terminalNeighborSetFintype] using
      H.sum_degrees_eq_twice_card_edges
  change terminals.card ≤ 2
  omega

/-- In a proper two-color induced subgraph, two neighbors of the same
vertex carry the same color. -/
theorem bicolored_neighbor_colors_eq
    {W Alpha : Type*} {H : SimpleGraph W}
    (C : H.Coloring Alpha) (a b : Alpha)
    {center first second : C.bicoloredSet a b}
    (hfirst : (C.bicoloredSubgraph a b).Adj center first)
    (hsecond : (C.bicoloredSubgraph a b).Adj center second) :
    C first.1 = C second.1 := by
  have hcenterFirst : C center.1 ≠ C first.1 := C.valid hfirst
  have hcenterSecond : C center.1 ≠ C second.1 := C.valid hsecond
  rcases center.property with hcenter | hcenter <;>
    rcases first.property with hfirstColor | hfirstColor <;>
      rcases second.property with hsecondColor | hsecondColor
  all_goals
    first
    | exact hfirstColor.trans hsecondColor.symm
    | exact False.elim
        (hcenterFirst (hcenter.trans hfirstColor.symm))
    | exact False.elim
        (hcenterSecond (hcenter.trans hsecondColor.symm))

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance kempeEndpointGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

noncomputable local instance kempeEndpointBicoloredSetFintype
    (C : G.EdgeColoring Color) (a b : Color) :
    Fintype (C.bicoloredSet a b) := by
  classical
  exact Subtype.fintype _

noncomputable local instance kempeEndpointBicoloredNeighborSetFintype
    (C : G.EdgeColoring Color) (a b : Color)
    (edge : C.bicoloredSet a b) :
    Fintype ((C.bicoloredSubgraph a b).neighborSet edge) := by
  classical
  exact Subtype.fintype _

/-- Every bicolored edge-line subgraph of a proper edge coloring has maximum
degree at most two. -/
theorem bicoloredSubgraph_degree_le_two
    (C : G.EdgeColoring Color) (a b : Color)
    (edge : C.bicoloredSet a b) :
    (C.bicoloredSubgraph a b).degree edge ≤ 2 := by
  rw [← (C.bicoloredSubgraph a b).card_neighborFinset_eq_degree]
  by_contra hdegree
  have hthree :
      2 < ((C.bicoloredSubgraph a b).neighborFinset edge).card :=
    Nat.lt_of_not_ge hdegree
  rcases Finset.two_lt_card_iff.mp hthree with
    ⟨first, second, third, hfirst, hsecond, hthird,
      hfirstSecond, hfirstThird, hsecondThird⟩
  have hedgeFirst : G.lineGraph.Adj edge.1 first.1 := by
    simpa using hfirst
  have hedgeSecond : G.lineGraph.Adj edge.1 second.1 := by
    simpa using hsecond
  have hedgeThird : G.lineGraph.Adj edge.1 third.1 := by
    simpa using hthird
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeFirst with
    ⟨hedgeFirstNe, firstCommon, hfirstCommonEdge, hfirstCommonFirst⟩
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeSecond with
    ⟨hedgeSecondNe, secondCommon, hsecondCommonEdge, hsecondCommonSecond⟩
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeThird with
    ⟨hedgeThirdNe, thirdCommon, hthirdCommonEdge, hthirdCommonThird⟩
  have hcommonNotPairwise :
      ¬ (firstCommon ≠ secondCommon ∧
        firstCommon ≠ thirdCommon ∧
        secondCommon ≠ thirdCommon) := by
    intro hpairwise
    have htooMany : 2 < edge.1.1.toFinset.card :=
      Finset.two_lt_card_iff.mpr
        ⟨firstCommon, secondCommon, thirdCommon,
          by simpa using hfirstCommonEdge,
          by simpa using hsecondCommonEdge,
          by simpa using hthirdCommonEdge,
          hpairwise.1, hpairwise.2.1, hpairwise.2.2⟩
    have hcard : edge.1.1.toFinset.card = 2 :=
      Sym2.card_toFinset_of_not_isDiag edge.1.1
        (G.not_isDiag_of_mem_edgeSet edge.1.2)
    omega
  have hfirstNeighbor :
      (C.bicoloredSubgraph a b).Adj edge first := by
    simpa using hfirst
  have hsecondNeighbor :
      (C.bicoloredSubgraph a b).Adj edge second := by
    simpa using hsecond
  have hthirdNeighbor :
      (C.bicoloredSubgraph a b).Adj edge third := by
    simpa using hthird
  by_cases hfirstSecondCommon : firstCommon = secondCommon
  · have hfirstSecondVal : first.1 ≠ second.1 := by
      intro heq
      exact hfirstSecond (Subtype.ext heq)
    have hfirstSecondAdj : G.lineGraph.Adj first.1 second.1 :=
      (SimpleGraph.lineGraph_adj_iff_exists).2
        ⟨hfirstSecondVal, firstCommon, hfirstCommonFirst, by
          simpa [hfirstSecondCommon] using hsecondCommonSecond⟩
    exact C.valid hfirstSecondAdj
      (bicolored_neighbor_colors_eq C a b
        hfirstNeighbor hsecondNeighbor)
  · by_cases hfirstThirdCommon : firstCommon = thirdCommon
    · have hfirstThirdVal : first.1 ≠ third.1 := by
        intro heq
        exact hfirstThird (Subtype.ext heq)
      have hfirstThirdAdj : G.lineGraph.Adj first.1 third.1 :=
        (SimpleGraph.lineGraph_adj_iff_exists).2
          ⟨hfirstThirdVal, firstCommon, hfirstCommonFirst, by
            simpa [hfirstThirdCommon] using hthirdCommonThird⟩
      exact C.valid hfirstThirdAdj
        (bicolored_neighbor_colors_eq C a b
          hfirstNeighbor hthirdNeighbor)
    · have hsecondThirdCommon : secondCommon = thirdCommon := by
        by_contra hne
        exact hcommonNotPairwise
          ⟨hfirstSecondCommon, hfirstThirdCommon, hne⟩
      have hsecondThirdVal : second.1 ≠ third.1 := by
        intro heq
        exact hsecondThird (Subtype.ext heq)
      have hsecondThirdAdj : G.lineGraph.Adj second.1 third.1 :=
        (SimpleGraph.lineGraph_adj_iff_exists).2
          ⟨hsecondThirdVal, secondCommon, hsecondCommonSecond, by
            simpa [hsecondThirdCommon] using hthirdCommonThird⟩
      exact C.valid hsecondThirdAdj
        (bicolored_neighbor_colors_eq C a b
          hsecondNeighbor hthirdNeighbor)

/-- Instance-independent cardinal form of the bicolored maximum-degree
bound. -/
theorem bicoloredSubgraph_neighborSet_ncard_le_two
    (C : G.EdgeColoring Color) (a b : Color)
    (edge : C.bicoloredSet a b) :
    ((C.bicoloredSubgraph a b).neighborSet edge).ncard ≤ 2 := by
  calc
    ((C.bicoloredSubgraph a b).neighborSet edge).ncard =
        Fintype.card ((C.bicoloredSubgraph a b).neighborSet edge) :=
      (Set.fintypeCard_eq_ncard _).symm
    _ = (C.bicoloredSubgraph a b).degree edge :=
      (C.bicoloredSubgraph a b).card_neighborSet_eq_degree edge
    _ ≤ 2 := bicoloredSubgraph_degree_le_two C a b edge

/-- If a selected pair terminates at one endpoint of an edge, that edge is
a terminal vertex of the corresponding bicolored line graph. -/
theorem bicoloredNeighborSet_subsingleton_of_selected_termination
    (C : G.EdgeColoring Color) {a b : Color} {edge : G.edgeSet} {vertex : V}
    (hselected : C edge = a ∨ C edge = b)
    (hterm : KempePairTerminatesAtVertex C a b edge vertex) :
    Set.Subsingleton
      ((C.bicoloredSubgraph a b).neighborSet ⟨edge, hselected⟩) := by
  intro first hfirst second hsecond
  apply Subtype.ext
  by_contra hne
  have hedgeFirst : G.lineGraph.Adj edge first.1 := hfirst
  have hedgeSecond : G.lineGraph.Adj edge second.1 := hsecond
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeFirst with
    ⟨hedgeFirstNe, firstCommon, hfirstCommonEdge, hfirstCommonFirst⟩
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeSecond with
    ⟨hedgeSecondNe, secondCommon, hsecondCommonEdge, hsecondCommonSecond⟩
  have hfirstCommonNe : firstCommon ≠ vertex := by
    intro heq
    subst firstCommon
    have hfirstIncident :
        first.1 ∈ incidentEdgeFinset G vertex := by
      simpa [incidentEdgeFinset] using hfirstCommonFirst
    rcases first.property with hcolor | hcolor
    · exact (hterm.2.2 first.1 hfirstIncident hedgeFirstNe.symm).1 hcolor
    · exact (hterm.2.2 first.1 hfirstIncident hedgeFirstNe.symm).2 hcolor
  have hsecondCommonNe : secondCommon ≠ vertex := by
    intro heq
    subst secondCommon
    have hsecondIncident :
        second.1 ∈ incidentEdgeFinset G vertex := by
      simpa [incidentEdgeFinset] using hsecondCommonSecond
    rcases second.property with hcolor | hcolor
    · exact (hterm.2.2 second.1 hsecondIncident hedgeSecondNe.symm).1 hcolor
    · exact (hterm.2.2 second.1 hsecondIncident hedgeSecondNe.symm).2 hcolor
  have hvertexEdge : vertex ∈ (edge : Sym2 V) := by
    simpa [incidentEdgeFinset] using hterm.1
  obtain ⟨other, hrepr⟩ := Sym2.mem_iff_exists.mp hvertexEdge
  have hfirstCases : firstCommon = vertex ∨ firstCommon = other := by
    rw [hrepr] at hfirstCommonEdge
    simpa using hfirstCommonEdge
  have hsecondCases : secondCommon = vertex ∨ secondCommon = other := by
    rw [hrepr] at hsecondCommonEdge
    simpa using hsecondCommonEdge
  have hcommon : firstCommon = secondCommon :=
    (hfirstCases.resolve_left hfirstCommonNe).trans
      (hsecondCases.resolve_left hsecondCommonNe).symm
  have hfirstSecondAdj : G.lineGraph.Adj first.1 second.1 :=
    (SimpleGraph.lineGraph_adj_iff_exists).2
      ⟨hne, firstCommon, hfirstCommonFirst, by
        simpa [hcommon] using hsecondCommonSecond⟩
  have hfirstNeighbor :
      (C.bicoloredSubgraph a b).Adj ⟨edge, hselected⟩ first := hfirst
  have hsecondNeighbor :
      (C.bicoloredSubgraph a b).Adj ⟨edge, hselected⟩ second := hsecond
  exact C.valid hfirstSecondAdj
    (bicolored_neighbor_colors_eq C a b hfirstNeighbor hsecondNeighbor)

/-- If one selected edge terminates at both of its distinct graph endpoints,
it is isolated in the bicolored line graph. -/
theorem bicoloredNeighborSet_eq_empty_of_selected_termination_at_distinct_vertices
    (C : G.EdgeColoring Color) {a b : Color} {edge : G.edgeSet}
    {firstVertex secondVertex : V}
    (hvertices : firstVertex ≠ secondVertex)
    (hselected : C edge = a ∨ C edge = b)
    (hfirstTerm :
      KempePairTerminatesAtVertex C a b edge firstVertex)
    (hsecondTerm :
      KempePairTerminatesAtVertex C a b edge secondVertex) :
    (C.bicoloredSubgraph a b).neighborSet ⟨edge, hselected⟩ = ∅ := by
  ext neighbor
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hneighbor
  have hedgeNeighbor : G.lineGraph.Adj edge neighbor.1 := hneighbor
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeNeighbor with
    ⟨hedgeNeighborNe, common, hcommonEdge, hcommonNeighbor⟩
  have hfirstEdge : firstVertex ∈ (edge : Sym2 V) := by
    simpa [incidentEdgeFinset] using hfirstTerm.1
  have hsecondEdge : secondVertex ∈ (edge : Sym2 V) := by
    simpa [incidentEdgeFinset] using hsecondTerm.1
  obtain ⟨other, hrepr⟩ := Sym2.mem_iff_exists.mp hfirstEdge
  have hother : other = secondVertex := by
    rw [hrepr] at hsecondEdge
    rcases (by simpa using hsecondEdge :
      secondVertex = firstVertex ∨ secondVertex = other) with h | h
    · exact False.elim (hvertices h.symm)
    · exact h.symm
  have hcommonCases : common = firstVertex ∨ common = secondVertex := by
    rw [hrepr, hother] at hcommonEdge
    simpa using hcommonEdge
  rcases hcommonCases with hcommon | hcommon
  · subst common
    have hneighborIncident :
        neighbor.1 ∈ incidentEdgeFinset G firstVertex := by
      simpa [incidentEdgeFinset] using hcommonNeighbor
    rcases neighbor.property with hcolor | hcolor
    · exact (hfirstTerm.2.2 neighbor.1 hneighborIncident
        hedgeNeighborNe.symm).1 hcolor
    · exact (hfirstTerm.2.2 neighbor.1 hneighborIncident
        hedgeNeighborNe.symm).2 hcolor
  · subst common
    have hneighborIncident :
        neighbor.1 ∈ incidentEdgeFinset G secondVertex := by
      simpa [incidentEdgeFinset] using hcommonNeighbor
    rcases neighbor.property with hcolor | hcolor
    · exact (hsecondTerm.2.2 neighbor.1 hneighborIncident
        hedgeNeighborNe.symm).1 hcolor
    · exact (hsecondTerm.2.2 neighbor.1 hneighborIncident
        hedgeNeighborNe.symm).2 hcolor

end GoertzelV24KempeEndpoint

namespace GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance reachabilityGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A selected request at a degree-two port leaves exactly one incident edge
in the selected two-color family. -/
theorem existsUnique_incident_bicolored_edge_of_colorWord_selected
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (port : Fin portCount)
    (hselected : data.colorWord C port = a ∨ data.colorWord C port = b) :
    ∃! edge : G.edgeSet,
      edge ∈ incidentEdgeFinset G (data.defectVertex port) ∧
        (C edge = a ∨ C edge = b) := by
  rcases Finset.card_eq_two.mp (hdata.2.1 port) with
    ⟨first, second, hne, hincident⟩
  have hsum : C first + C second = a ∨ C first + C second = b := by
    simpa [colorWord, vertexKirchhoffSum, hincident, hne] using hselected
  have hsummand := validColorPair_summand_selected_of_sum_selected
    a b hab (C first) (C second) hsum
  by_cases hfirst : C first = a ∨ C first = b
  · have hsecond : ¬ (C second = a ∨ C second = b) := by
      intro hsecond
      have hnot := validColorPair_add_not_selected_of_summands_selected
        a b hab (C first) (C second) hfirst hsecond
      exact hsum.elim hnot.1 hnot.2
    refine ⟨first, ?_, ?_⟩
    · rw [hincident]
      exact ⟨by simp, hfirst⟩
    · intro edge hedge
      rw [hincident] at hedge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge.1 with rfl | rfl
      · rfl
      · exact False.elim (hsecond hedge.2)
  · have hsecond : C second = a ∨ C second = b :=
      hsummand.resolve_left hfirst
    refine ⟨second, ?_, ?_⟩
    · rw [hincident]
      exact ⟨by simp, hsecond⟩
    · intro edge hedge
      rw [hincident] at hedge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge.1 with rfl | rfl
      · exact False.elim (hfirst hedge.2)
      · rfl

/-- The unique selected edge at a selected degree-two request is terminal at
that port in the selected Kempe family. -/
theorem kempePairTerminatesAtPort_of_colorWord_selected
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (port : Fin portCount)
    (hselected : data.colorWord C port = a ∨ data.colorWord C port = b)
    {edge : G.edgeSet}
    (hincident : edge ∈ incidentEdgeFinset G (data.defectVertex port))
    (hcolor : C edge = a ∨ C edge = b) :
    KempePairTerminatesAtVertex C a b edge (data.defectVertex port) := by
  rcases data.existsUnique_incident_bicolored_edge_of_colorWord_selected
      hdata C hab port hselected with
    ⟨selectedEdge, hselectedEdge, hunique⟩
  have hedgeEq : edge = selectedEdge := hunique edge ⟨hincident, hcolor⟩
  refine ⟨hincident, hcolor, ?_⟩
  intro other hotherIncident hotherNe
  constructor
  · intro hotherColor
    have hotherEq := hunique other
      ⟨hotherIncident, Or.inl hotherColor⟩
    exact hotherNe (hotherEq.trans hedgeEq.symm)
  · intro hotherColor
    have hotherEq := hunique other
      ⟨hotherIncident, Or.inr hotherColor⟩
    exact hotherNe (hotherEq.trans hedgeEq.symm)

/-- The selected incidence at a selected degree-two request is a terminal
vertex of the bicolored line graph. -/
theorem bicoloredNeighborSet_subsingleton_of_colorWord_selected
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (port : Fin portCount)
    (hselected : data.colorWord C port = a ∨ data.colorWord C port = b)
    {edge : G.edgeSet}
    (hincident : edge ∈ incidentEdgeFinset G (data.defectVertex port))
    (hcolor : C edge = a ∨ C edge = b) :
    Set.Subsingleton
      ((C.bicoloredSubgraph a b).neighborSet ⟨edge, hcolor⟩) := by
  apply GoertzelV24KempeEndpoint.bicoloredNeighborSet_subsingleton_of_selected_termination
    C hcolor
  exact data.kempePairTerminatesAtPort_of_colorWord_selected
    hdata C hab port hselected hincident hcolor

/-- No selected bicolored component can terminate at all four distinct ports
of a well-formed four-port boundary. -/
theorem not_exists_allPort_kempeComponent
    (data : DegreeTwoBoundaryData G 4)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (hselected : ∀ port : Fin 4,
      data.colorWord C port = a ∨ data.colorWord C port = b) :
    ¬ ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      data.kempePortSupport C a b K = Finset.univ := by
  classical
  rintro ⟨K, hsupport⟩
  let H := C.bicoloredSubgraph a b
  have hmeets : ∀ port : Fin 4,
      data.KempeComponentMeetsPort C a b K port := by
    intro port
    apply (data.mem_kempePortSupport_iff C a b K port).1
    rw [hsupport]
    simp
  let portEdge : Fin 4 → G.edgeSet := fun port =>
    Classical.choose (hmeets port)
  have hportEdgeIncident : ∀ port : Fin 4,
      portEdge port ∈ incidentEdgeFinset G (data.defectVertex port) := by
    intro port
    exact (Classical.choose_spec (hmeets port)).1
  have hportEdgeMember : ∀ port : Fin 4,
      portEdge port ∈ C.kempeComponentSet a b K := by
    intro port
    exact (Classical.choose_spec (hmeets port)).2
  have hportEdgeColor : ∀ port : Fin 4,
      C (portEdge port) = a ∨ C (portEdge port) = b := by
    intro port
    exact C.mem_bicoloredSet_of_mem_kempeComponentSet
      (hportEdgeMember port)
  let portVertex : Fin 4 → C.bicoloredSet a b := fun port =>
    ⟨portEdge port, hportEdgeColor port⟩
  have hportVertexComponent : ∀ port : Fin 4,
      H.connectedComponentMk (portVertex port) = K := by
    intro port
    exact (hportEdgeMember port).2
  let componentPortVertex : Fin 4 → K := fun port =>
    ⟨portVertex port, hportVertexComponent port⟩
  have htermination : ∀ port : Fin 4,
      KempePairTerminatesAtVertex C a b (portEdge port)
        (data.defectVertex port) := by
    intro port
    exact data.kempePairTerminatesAtPort_of_colorWord_selected
      hdata C hab port (hselected port) (hportEdgeIncident port)
        (hportEdgeColor port)
  have hterminalInH : ∀ port : Fin 4,
      (H.neighborSet (portVertex port)).Subsingleton := by
    intro port
    exact data.bicoloredNeighborSet_subsingleton_of_colorWord_selected
      hdata C hab port (hselected port) (hportEdgeIncident port)
        (hportEdgeColor port)
  have hdegreeComponent : ∀ vertex : K,
      (K.toSimpleGraph.neighborSet vertex).ncard ≤ 2 := by
    intro vertex
    let toParent : K.toSimpleGraph.neighborSet vertex →
        H.neighborSet vertex.1 := fun neighbor =>
      ⟨neighbor.1.1,
        show H.Adj vertex.1 neighbor.1.1 from neighbor.2⟩
    let toComponent : H.neighborSet vertex.1 →
        K.toSimpleGraph.neighborSet vertex := fun neighbor => by
      let neighborInK : K :=
        ⟨neighbor.1,
          K.mem_supp_of_adj_mem_supp vertex.2 neighbor.2⟩
      exact ⟨neighborInK,
        show K.toSimpleGraph.Adj vertex neighborInK from neighbor.2⟩
    let neighborEquiv :
        K.toSimpleGraph.neighborSet vertex ≃ H.neighborSet vertex.1 :=
      { toFun := toParent
        invFun := toComponent
        left_inv := by
          intro neighbor
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro neighbor
          apply Subtype.ext
          rfl }
    calc
      (K.toSimpleGraph.neighborSet vertex).ncard =
          (H.neighborSet vertex.1).ncard :=
        Set.ncard_congr' neighborEquiv
      _ ≤ 2 :=
        GoertzelV24KempeEndpoint.bicoloredSubgraph_neighborSet_ncard_le_two
          C a b vertex.1
  have hterminalInComponent : ∀ port : Fin 4,
      (K.toSimpleGraph.neighborSet (componentPortVertex port)).Subsingleton := by
    intro port first hfirst second hsecond
    apply Subtype.ext
    apply hterminalInH port
    · exact hfirst
    · exact hsecond
  by_cases hinjective : Function.Injective componentPortVertex
  · let terminalVertices := Finset.univ.filter fun vertex : K =>
      (K.toSimpleGraph.neighborSet vertex).Subsingleton
    let portImage := Finset.univ.image componentPortVertex
    have himageSubset : portImage ⊆ terminalVertices := by
      intro vertex hvertex
      rcases Finset.mem_image.mp hvertex with ⟨port, _hport, rfl⟩
      simp only [terminalVertices, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact hterminalInComponent port
    have himageCard : portImage.card = 4 := by
      simp [portImage, Finset.card_image_of_injective _ hinjective]
    have hterminalCard : terminalVertices.card ≤ 2 := by
      exact GoertzelV24KempeEndpoint.terminalVertices_card_le_two
        K.toSimpleGraph K.connected_toSimpleGraph hdegreeComponent
    have hcardLe := Finset.card_le_card himageSubset
    omega
  · rw [Function.Injective] at hinjective
    push Not at hinjective
    rcases hinjective with ⟨first, second, heq, hne⟩
    have hedgeEq : portEdge first = portEdge second := by
      exact congrArg (fun vertex : K => vertex.1.1) heq
    have hdefectNe : data.defectVertex first ≠ data.defectVertex second := by
      intro hvertices
      exact hne (hdata.1 hvertices)
    have hsecondTermination :
        KempePairTerminatesAtVertex C a b (portEdge first)
          (data.defectVertex second) := by
      rw [hedgeEq]
      exact htermination second
    have hisolated :
        H.neighborSet (portVertex first) = ∅ := by
      exact GoertzelV24KempeEndpoint.bicoloredNeighborSet_eq_empty_of_selected_termination_at_distinct_vertices
        C hdefectNe (hportEdgeColor first) (htermination first)
          hsecondTermination
    obtain ⟨third, hthirdFirst, hthirdSecond⟩ :=
      ENat.exists_ne_ne_of_three_le (α := Fin 4)
        (by norm_num [ENat.card, Nat.card_eq_fintype_card]) first second
    have hreach : H.Reachable (portVertex first) (portVertex third) :=
      ConnectedComponent.eq.mp
        ((hportVertexComponent first).trans
          (hportVertexComponent third).symm)
    have hportVertexEq : portVertex first = portVertex third := by
      by_contra hvertexNe
      exact H.not_reachable_of_neighborSet_left_eq_empty
        hvertexNe hisolated hreach
    have hthirdEdgeEq : portEdge first = portEdge third :=
      congrArg Subtype.val hportVertexEq
    have hfirstVertexMem :
        data.defectVertex first ∈ (portEdge first).1.toFinset := by
      simpa [incidentEdgeFinset] using hportEdgeIncident first
    have hsecondVertexMem :
        data.defectVertex second ∈ (portEdge first).1.toFinset := by
      simpa [incidentEdgeFinset, hedgeEq] using hportEdgeIncident second
    have hthirdVertexMem :
        data.defectVertex third ∈ (portEdge first).1.toFinset := by
      simpa [incidentEdgeFinset, hthirdEdgeEq] using hportEdgeIncident third
    have hfirstThird :
        data.defectVertex first ≠ data.defectVertex third := by
      intro hvertices
      exact hthirdFirst (hdata.1 hvertices).symm
    have hsecondThird :
        data.defectVertex second ≠ data.defectVertex third := by
      intro hvertices
      exact hthirdSecond (hdata.1 hvertices).symm
    have htooMany : 2 < (portEdge first).1.toFinset.card :=
      Finset.two_lt_card_iff.mpr
        ⟨data.defectVertex first, data.defectVertex second,
          data.defectVertex third, hfirstVertexMem, hsecondVertexMem,
          hthirdVertexMem, hdefectNe, hfirstThird, hsecondThird⟩
    have hcard : (portEdge first).1.toFinset.card = 2 :=
      Sym2.card_toFinset_of_not_isDiag (portEdge first).1
        (G.not_isDiag_of_mem_edgeSet (portEdge first).2)
    omega

/-- Exactly two boundary components, with the two cyclic same-side supports,
exhaust the selected four-port Kempe cut. -/
def HasTwoSameSideKempeCutProfile
    (data : DegreeTwoBoundaryData G 4)
    (C : G.EdgeColoring Color) (a b : Color) : Prop :=
  ∃ K01 K23 : (C.bicoloredSubgraph a b).ConnectedComponent,
    K01 ≠ K23 ∧
    data.kempePortSupport C a b K01 = {0, 1} ∧
    data.kempePortSupport C a b K23 = {2, 3} ∧
    ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      (data.kempePortSupport C a b K).Nonempty →
        K = K01 ∨ K = K23

/-- Terminality eliminates the one-component branch of the exact cut
classification. -/
theorem hasTwoSameSideKempeCutProfile_of_exactProfile
    (data : DegreeTwoBoundaryData G 4)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (hselected : ∀ port : Fin 4,
      data.colorWord C port = a ∨ data.colorWord C port = b)
    (hprofile : data.HasExactSameSideKempeCutProfile C a b) :
    data.HasTwoSameSideKempeCutProfile C a b := by
  rcases hprofile with hall | htwo
  · exfalso
    apply data.not_exists_allPort_kempeComponent hdata C hab hselected
    exact ⟨hall.choose, hall.choose_spec.1⟩
  · exact htwo

/-- Paired incidence and four selected requests force exactly two, rather
than merely one or two, same-side boundary components. -/
theorem exists_two_sameSide_kempeComponents
    (data : DegreeTwoBoundaryData G 4)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) {a b : Color}
    (hab : ValidColorPair a b)
    (hselected : ∀ port : Fin 4,
      data.colorWord C port = a ∨ data.colorWord C port = b)
    (hpaired : ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      (data.KempeComponentMeetsPort C a b K 0 ↔
        data.KempeComponentMeetsPort C a b K 1) ∧
      (data.KempeComponentMeetsPort C a b K 2 ↔
        data.KempeComponentMeetsPort C a b K 3)) :
    data.HasTwoSameSideKempeCutProfile C a b := by
  apply data.hasTwoSameSideKempeCutProfile_of_exactProfile
    hdata C hab hselected
  exact data.exists_one_allPort_or_two_sameSide_kempeComponents
    hdata C hab hselected hpaired

/-- Two ports are joined by the selected Kempe family when selected incident
edges at the ports are reachable in its bicolored line graph. -/
def KempePortsConnected {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (left right : Fin portCount) : Prop :=
  ∃ leftEdge rightEdge : C.bicoloredSet a b,
    leftEdge.1 ∈ incidentEdgeFinset G (data.defectVertex left) ∧
    rightEdge.1 ∈ incidentEdgeFinset G (data.defectVertex right) ∧
    (C.bicoloredSubgraph a b).Reachable leftEdge rightEdge

/-- Port connectivity is exactly common incidence with one labeled Kempe
component. -/
theorem kempePortsConnected_iff_exists_component_meets_both
    {portCount : Nat}
    (data : DegreeTwoBoundaryData G portCount)
    (C : G.EdgeColoring Color) (a b : Color)
    (left right : Fin portCount) :
    data.KempePortsConnected C a b left right ↔
      ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
        data.KempeComponentMeetsPort C a b K left ∧
        data.KempeComponentMeetsPort C a b K right := by
  constructor
  · rintro ⟨leftEdge, rightEdge, hleftIncident, hrightIncident, hreach⟩
    let K := (C.bicoloredSubgraph a b).connectedComponentMk leftEdge
    refine ⟨K, ⟨leftEdge, hleftIncident, ?_⟩,
      ⟨rightEdge, hrightIncident, ?_⟩⟩
    · exact C.mem_kempeComponentSet_self leftEdge.property
    · exact ⟨rightEdge.property, (ConnectedComponent.eq.mpr hreach).symm⟩
  · rintro ⟨K, ⟨leftEdge, hleftIncident, hleft⟩,
      ⟨rightEdge, hrightIncident, hright⟩⟩
    rcases hleft with ⟨hleftColor, hleftComponent⟩
    rcases hright with ⟨hrightColor, hrightComponent⟩
    refine ⟨⟨leftEdge, hleftColor⟩, ⟨rightEdge, hrightColor⟩,
      hleftIncident, hrightIncident, ?_⟩
    exact ConnectedComponent.eq.mp
      (hleftComponent.trans hrightComponent.symm)

/-- The exact boundary reachability relation whose two classes are the
cyclic same-side port pairs `{0,1}` and `{2,3}`. -/
def HasSameSideKempeReachabilityProfile
    (data : DegreeTwoBoundaryData G 4)
    (C : G.EdgeColoring Color) (a b : Color) : Prop :=
  ∀ left right : Fin 4,
    data.KempePortsConnected C a b left right ↔
      (left ∈ ({0, 1} : Finset (Fin 4)) ↔
        right ∈ ({0, 1} : Finset (Fin 4)))

/-- The exactly-two component cut profile induces the corresponding exact
reachability partition on the four boundary ports. -/
theorem hasSameSideKempeReachabilityProfile_of_twoComponentProfile
    (data : DegreeTwoBoundaryData G 4)
    (C : G.EdgeColoring Color) (a b : Color)
    (hprofile : data.HasTwoSameSideKempeCutProfile C a b) :
    data.HasSameSideKempeReachabilityProfile C a b := by
  classical
  rcases hprofile with
    ⟨K01, K23, _hne, hsupport01, hsupport23, hexhaust⟩
  have hpartition : ∀ port : Fin 4,
      port ∈ ({2, 3} : Finset (Fin 4)) ↔
        port ∉ ({0, 1} : Finset (Fin 4)) := by
    intro port
    fin_cases port <;> decide
  intro left right
  rw [data.kempePortsConnected_iff_exists_component_meets_both]
  constructor
  · rintro ⟨K, hleft, hright⟩
    have hnonempty : (data.kempePortSupport C a b K).Nonempty :=
      ⟨left, (data.mem_kempePortSupport_iff C a b K left).2 hleft⟩
    rcases hexhaust K hnonempty with hK | hK
    · have hleftK01 :
          data.KempeComponentMeetsPort C a b K01 left := by
        simpa [hK] using hleft
      have hrightK01 :
          data.KempeComponentMeetsPort C a b K01 right := by
        simpa [hK] using hright
      have hleft01 : left ∈ ({0, 1} : Finset (Fin 4)) := by
        rw [← hsupport01]
        exact (data.mem_kempePortSupport_iff C a b K01 left).2 hleftK01
      have hright01 : right ∈ ({0, 1} : Finset (Fin 4)) := by
        rw [← hsupport01]
        exact (data.mem_kempePortSupport_iff C a b K01 right).2 hrightK01
      exact iff_of_true hleft01 hright01
    · have hleftK23 :
          data.KempeComponentMeetsPort C a b K23 left := by
        simpa [hK] using hleft
      have hrightK23 :
          data.KempeComponentMeetsPort C a b K23 right := by
        simpa [hK] using hright
      have hleft23 : left ∈ ({2, 3} : Finset (Fin 4)) := by
        rw [← hsupport23]
        exact (data.mem_kempePortSupport_iff C a b K23 left).2 hleftK23
      have hright23 : right ∈ ({2, 3} : Finset (Fin 4)) := by
        rw [← hsupport23]
        exact (data.mem_kempePortSupport_iff C a b K23 right).2 hrightK23
      exact iff_of_false ((hpartition left).1 hleft23)
        ((hpartition right).1 hright23)
  · intro hside
    by_cases hleft01 : left ∈ ({0, 1} : Finset (Fin 4))
    · have hright01 : right ∈ ({0, 1} : Finset (Fin 4)) :=
        hside.1 hleft01
      refine ⟨K01, ?_, ?_⟩
      · apply (data.mem_kempePortSupport_iff C a b K01 left).1
        rw [hsupport01]
        exact hleft01
      · apply (data.mem_kempePortSupport_iff C a b K01 right).1
        rw [hsupport01]
        exact hright01
    · have hright01 : right ∉ ({0, 1} : Finset (Fin 4)) := by
        intro hright
        exact hleft01 (hside.2 hright)
      refine ⟨K23, ?_, ?_⟩
      · apply (data.mem_kempePortSupport_iff C a b K23 left).1
        rw [hsupport23]
        exact (hpartition left).2 hleft01
      · apply (data.mem_kempePortSupport_iff C a b K23 right).1
        rw [hsupport23]
        exact (hpartition right).2 hright01

end

end GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

open GoertzelV24AdjacentPairBoundary

namespace GoertzelV24AdjacentPairBoundary.AdjacentPairData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance exactReachabilityGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet := Subtype.instDecidableEq

local instance exactReachabilityRetainedVertexSetFintype
    (first second : V) : Fintype (retainedVertexSet first second) :=
  Subtype.fintype _

local instance exactReachabilityRetainedVertexSetDecidableEq
    (first second : V) : DecidableEq (retainedVertexSet first second) :=
  Subtype.instDecidableEq

/-- Terminality sharpens the bundled one-or-two cut classification to
exactly two same-side components. -/
theorem CyclicKempeProfile.hasTwoSameSideKempeCutProfile
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data) :
    data.degreeTwoBoundaryData.HasTwoSameSideKempeCutProfile
      profile.coloring profile.firstColor profile.secondColor := by
  have hsame :
      data.degreeTwoBoundaryData.colorWord profile.coloring 0 =
          data.degreeTwoBoundaryData.colorWord profile.coloring 1 ∧
        data.degreeTwoBoundaryData.colorWord profile.coloring 2 =
          data.degreeTwoBoundaryData.colorWord profile.coloring 3 := by
    simpa [SquareReductionSide.Compatible,
      SquareReductionSide.join01_23] using profile.reductionCompatible
  have hselected : ∀ port : Fin 4,
      data.degreeTwoBoundaryData.colorWord profile.coloring port =
          profile.firstColor ∨
        data.degreeTwoBoundaryData.colorWord profile.coloring port =
          profile.secondColor := by
    intro port
    fin_cases port
    · exact profile.firstRequestSelected
    · rcases profile.firstRequestSelected with hfirst | hsecond
      · exact Or.inl (hsame.1.symm.trans hfirst)
      · exact Or.inr (hsame.1.symm.trans hsecond)
    · exact profile.secondRequestSelected
    · rcases profile.secondRequestSelected with hfirst | hsecond
      · exact Or.inl (hsame.2.symm.trans hfirst)
      · exact Or.inr (hsame.2.symm.trans hsecond)
  exact data.degreeTwoBoundaryData.hasTwoSameSideKempeCutProfile_of_exactProfile
    profile.boundaryWellFormed profile.coloring profile.validPair hselected
      profile.hasExactSameSideKempeCutProfile

/-- The graph-backed cyclic Kempe profile has exactly the two cyclic
same-side reachability classes. -/
theorem CyclicKempeProfile.hasSameSideKempeReachabilityProfile
    {graphData : SimpleGraphDartRotation.Data G}
    {data : AdjacentPairData G}
    (profile : CyclicKempeProfile graphData data) :
    data.degreeTwoBoundaryData.HasSameSideKempeReachabilityProfile
      profile.coloring profile.firstColor profile.secondColor :=
  data.degreeTwoBoundaryData.hasSameSideKempeReachabilityProfile_of_twoComponentProfile
    profile.coloring profile.firstColor profile.secondColor
      profile.hasTwoSameSideKempeCutProfile

end


end GoertzelV24AdjacentPairBoundary.AdjacentPairData

end Mettapedia.GraphTheory.FourColor
