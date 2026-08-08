import Mettapedia.GraphTheory.FourColor.GoertzelV24BetweenRegionMoves

/-!
# Noncircuit framed components meet the trail defects

This module identifies the graph-theoretic shape of the noncircuit residue
isolated in `GoertzelV24BetweenRegionMoves`.  A proper Tait coloring uses all
three nonzero colors at every cubic vertex.  Hence a selected two-color
component has two line-graph neighbors at every edge whose two endpoints are
cubic.  A legal framed component cannot meet a frozen interface stub, so any
failure of circuit regularity must occur at one of the two degree-two trail
defects.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  [Fintype G.edgeSet] [DecidableEq G.edgeSet]

/-- In a proper two-color induced graph, two neighbors of one selected edge
carry the same color.  This small generic fact is kept here so the L10 seam
does not import the much larger adjacent-pair profile stack. -/
private theorem bicolored_neighbor_colors_eq
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

noncomputable local instance bicoloredSetFintype
    (C : G.EdgeColoring Color) (a b : Color) :
    Fintype (C.bicoloredSet a b) := by
  classical
  exact Subtype.fintype _

noncomputable local instance bicoloredNeighborSetFintype
    (C : G.EdgeColoring Color) (a b : Color)
    (edge : C.bicoloredSet a b) :
    Fintype ((C.bicoloredSubgraph a b).neighborSet edge) := by
  classical
  exact Subtype.fintype _

/-- A selected edge has at most two neighbors in a bicolored line graph: at
most one selected neighbor can use each of the original edge's endpoints. -/
private theorem bicoloredSubgraph_degree_le_two
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
    ⟨_hedgeFirstNe, firstCommon, hfirstCommonEdge,
      hfirstCommonFirst⟩
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeSecond with
    ⟨_hedgeSecondNe, secondCommon, hsecondCommonEdge,
      hsecondCommonSecond⟩
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hedgeThird with
    ⟨_hedgeThirdNe, thirdCommon, hthirdCommonEdge,
      hthirdCommonThird⟩
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
      (bicolored_neighbor_colors_eq C a b hfirstNeighbor hsecondNeighbor)
  · by_cases hfirstThirdCommon : firstCommon = thirdCommon
    · have hfirstThirdVal : first.1 ≠ third.1 := by
        intro heq
        exact hfirstThird (Subtype.ext heq)
      have hfirstThirdAdj : G.lineGraph.Adj first.1 third.1 :=
        (SimpleGraph.lineGraph_adj_iff_exists).2
          ⟨hfirstThirdVal, firstCommon, hfirstCommonFirst, by
            simpa [hfirstThirdCommon] using hthirdCommonThird⟩
      exact C.valid hfirstThirdAdj
        (bicolored_neighbor_colors_eq C a b hfirstNeighbor hthirdNeighbor)
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
        (bicolored_neighbor_colors_eq C a b hsecondNeighbor hthirdNeighbor)

/-- Cardinal form of the local bicolored maximum-degree bound. -/
private theorem bicoloredSubgraph_neighborSet_ncard_le_two
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

/-- A selected Kempe component meets a trail defect when one of its original
graph edges is incident to one of the two distinguished degree-two vertices. -/
def KempeComponentMeetsDefect
    (data : FramedTrailData G)
    (C : G.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) : Prop :=
  ∃ i : Fin 2, ∃ edge : G.edgeSet,
    edge ∈ C.kempeComponentSet a b K ∧
      edge ∈ incidentEdgeFinset G (data.defectVertex i)

/-- Every endpoint of a selected component is a trail-defect incidence.  Here
"endpoint" is expressed intrinsically in the bicolored line graph as failure
of degree two; this also covers the degenerate isolated-component case. -/
def KempeComponentEndsOnlyAtDefects
    (data : FramedTrailData G)
    (C : G.EdgeColoring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) : Prop :=
  ∀ componentEdge : K,
    (K.toSimpleGraph.neighborSet componentEdge).ncard ≠ 2 →
      ∃ i : Fin 2,
        componentEdge.1.1 ∈
          incidentEdgeFinset G (data.defectVertex i)

/-- The noncircuit framed residue with its source-relevant endpoint fact made
explicit: the component is legal, noncircuit, and meets a trail defect. -/
def DefectPathFramedKempeStep
    (data : FramedTrailData G)
    (C C' : G.EdgeColoring Color) : Prop :=
  ∃ a b : Color,
    ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      ValidColorPair a b ∧
      ¬IsCircuitKempeComponent C a b K ∧
      KempeComponentEndsOnlyAtDefects data C a b K ∧
      KempeComponentMeetsDefect data C a b K ∧
      Disjoint (C.kempeComponentSet a b K)
        (data.frozenInterfaceEdges : Set G.edgeSet) ∧
      C' = C.swapOnKempeComponent a b K

/-- The neighbor set of a vertex inside a connected component is canonically
equivalent to its neighbor set in the parent graph: adjacency cannot leave a
connected component. -/
def connectedComponentNeighborEquiv
    {W : Type*} {H : SimpleGraph W}
    (K : H.ConnectedComponent) (vertex : K) :
    K.toSimpleGraph.neighborSet vertex ≃ H.neighborSet vertex.1 := by
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
  exact
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

/-- Cardinal form of `connectedComponentNeighborEquiv`. -/
theorem connectedComponent_neighborSet_ncard_eq_parent
    {W : Type*} {H : SimpleGraph W}
    (K : H.ConnectedComponent) (vertex : K) :
    (K.toSimpleGraph.neighborSet vertex).ncard =
      (H.neighborSet vertex.1).ncard :=
  Set.ncard_congr' (connectedComponentNeighborEquiv K vertex)

omit [Fintype V] [DecidableRel G.Adj] in
/-- At a cubic vertex of a Tait-colored graph, every nonzero Tait color occurs
on one of the three incident edges. -/
theorem exists_incident_edge_of_color_of_cubic_tait
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (vertex : V)
    (hcubic : (incidentEdgeFinset G vertex).card = 3)
    (target : Color) (htarget : target ≠ 0) :
    ∃ edge : G.edgeSet,
      edge ∈ incidentEdgeFinset G vertex ∧ C edge = target := by
  let incidentColors : Finset Color :=
    (incidentEdgeFinset G vertex).image C
  have hinjective : Set.InjOn C (incidentEdgeFinset G vertex : Set G.edgeSet) := by
    intro first hfirst second hsecond hcolors
    by_contra hne
    have hfirstAt : vertex ∈ (first : Sym2 V) := by
      simpa [incidentEdgeFinset] using hfirst
    have hsecondAt : vertex ∈ (second : Sym2 V) := by
      simpa [incidentEdgeFinset] using hsecond
    exact C.valid
      (G.lineGraph_adj_of_edgeSet_common_vertex hne hfirstAt hsecondAt)
      hcolors
  have hcard : incidentColors.card = 3 := by
    change ((incidentEdgeFinset G vertex).image C).card = 3
    rw [Finset.card_image_of_injOn hinjective, hcubic]
  have hsubset : incidentColors ⊆ (Finset.univ.erase (0 : Color)) := by
    intro color hcolor
    rcases Finset.mem_image.mp hcolor with ⟨edge, _hedge, rfl⟩
    simp [hC edge]
  have hunivCard : (Finset.univ.erase (0 : Color)).card = 3 := by
    decide
  have heq : incidentColors = Finset.univ.erase (0 : Color) :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  have htargetMem : target ∈ incidentColors := by
    rw [heq]
    simp [htarget]
  rcases Finset.mem_image.mp htargetMem with ⟨edge, hedge, hcolor⟩
  exact ⟨edge, hedge, hcolor⟩

/-- A selected edge whose two graph endpoints are cubic is an internal vertex
of its bicolored line graph: it has exactly two selected neighbors, one through
each endpoint. -/
theorem bicoloredSubgraph_neighborSet_ncard_eq_two_of_endpoint_cubic
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (edge : G.edgeSet) (hselected : C edge = a ∨ C edge = b)
    (hendpointCubic : ∀ vertex ∈ (edge : Sym2 V),
      (incidentEdgeFinset G vertex).card = 3) :
    ((C.bicoloredSubgraph a b).neighborSet ⟨edge, hselected⟩).ncard = 2 := by
  let firstEndpoint : V := edge.1.out.1
  let secondEndpoint : V := edge.1.out.2
  have hfirstMem : firstEndpoint ∈ (edge : Sym2 V) := by
    exact Sym2.out_fst_mem edge.1
  have hsecondMem : secondEndpoint ∈ (edge : Sym2 V) := by
    exact Sym2.out_snd_mem edge.1
  have hedgeRep : edge.1 = s(firstEndpoint, secondEndpoint) := by
    exact edge.1.out_eq.symm
  have hendpointsNe : firstEndpoint ≠ secondEndpoint := by
    intro heq
    have hdiag : edge.1.IsDiag := by
      rw [hedgeRep, Sym2.mk_isDiag_iff]
      exact heq
    exact G.not_isDiag_of_mem_edgeSet edge.2 hdiag
  let target : Color := if C edge = a then b else a
  have htargetNonzero : target ≠ 0 := by
    by_cases hcolor : C edge = a
    · simpa [target, hcolor] using hab.2.1
    · simpa [target, hcolor] using hab.1
  have htargetSelected : target = a ∨ target = b := by
    by_cases hcolor : C edge = a
    · exact Or.inr (by simp [target, hcolor])
    · exact Or.inl (by simp [target, hcolor])
  have htargetNe : C edge ≠ target := by
    by_cases hcolor : C edge = a
    · simpa [target, hcolor] using hab.2.2
    · have hedgeColor : C edge = b := hselected.resolve_left hcolor
      simpa [target, hcolor, hedgeColor] using hab.2.2.symm
  rcases exists_incident_edge_of_color_of_cubic_tait C hC
      firstEndpoint (hendpointCubic firstEndpoint hfirstMem)
      target htargetNonzero with
    ⟨firstNeighbor, hfirstIncident, hfirstColor⟩
  rcases exists_incident_edge_of_color_of_cubic_tait C hC
      secondEndpoint (hendpointCubic secondEndpoint hsecondMem)
      target htargetNonzero with
    ⟨secondNeighbor, hsecondIncident, hsecondColor⟩
  have hfirstNeighborNe : edge ≠ firstNeighbor := by
    intro heq
    apply htargetNe
    rw [heq, hfirstColor]
  have hsecondNeighborNe : edge ≠ secondNeighbor := by
    intro heq
    apply htargetNe
    rw [heq, hsecondColor]
  have hfirstNeighborAt : firstEndpoint ∈ (firstNeighbor : Sym2 V) := by
    simpa [incidentEdgeFinset] using hfirstIncident
  have hsecondNeighborAt :
      secondEndpoint ∈ (secondNeighbor : Sym2 V) := by
    simpa [incidentEdgeFinset] using hsecondIncident
  have hneighborsNe : firstNeighbor ≠ secondNeighbor := by
    intro heq
    have hboth : edge.1 = firstNeighbor.1 :=
      Sym2.eq_of_ne_mem hendpointsNe hfirstMem hsecondMem
        hfirstNeighborAt (by simpa [heq] using hsecondNeighborAt)
    exact hfirstNeighborNe (Subtype.ext hboth)
  let selectedEdge : C.bicoloredSet a b := ⟨edge, hselected⟩
  let firstSelected : C.bicoloredSet a b :=
    ⟨firstNeighbor, htargetSelected.imp hfirstColor.trans hfirstColor.trans⟩
  let secondSelected : C.bicoloredSet a b :=
    ⟨secondNeighbor, htargetSelected.imp hsecondColor.trans hsecondColor.trans⟩
  have hfirstAdj :
      (C.bicoloredSubgraph a b).Adj selectedEdge firstSelected := by
    exact G.lineGraph_adj_of_edgeSet_common_vertex hfirstNeighborNe
      hfirstMem hfirstNeighborAt
  have hsecondAdj :
      (C.bicoloredSubgraph a b).Adj selectedEdge secondSelected := by
    exact G.lineGraph_adj_of_edgeSet_common_vertex hsecondNeighborNe
      hsecondMem hsecondNeighborAt
  have hselectedNeighborsNe : firstSelected ≠ secondSelected := by
    intro heq
    exact hneighborsNe (congrArg Subtype.val heq)
  have hpairSubset :
      ({firstSelected, secondSelected} : Set (C.bicoloredSet a b)) ⊆
        (C.bicoloredSubgraph a b).neighborSet selectedEdge := by
    intro neighbor hneighbor
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hneighbor
    rcases hneighbor with rfl | hneighbor
    · exact hfirstAdj
    · subst neighbor
      exact hsecondAdj
  apply Nat.le_antisymm
  · exact bicoloredSubgraph_neighborSet_ncard_le_two C a b selectedEdge
  · calc
      2 = ({firstSelected, secondSelected} : Set
          (C.bicoloredSet a b)).ncard := by
        simp [hselectedNeighborsNe]
      _ ≤ ((C.bicoloredSubgraph a b).neighborSet selectedEdge).ncard :=
        Set.ncard_le_ncard hpairSubset

/-- Every non-degree-two vertex of a legal selected component lies on a trail
defect.  Frozen stubs cannot account for a missing line-graph neighbor because
legality excludes their incident edges; every remaining nondefect endpoint is
cubic by frame well-formedness. -/
theorem kempeComponentEndsOnlyAtDefects_of_legal
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hfrozen : Disjoint (C.kempeComponentSet a b K)
      (data.frozenInterfaceEdges : Set G.edgeSet)) :
    KempeComponentEndsOnlyAtDefects data C a b K := by
  intro componentEdge hdegree
  by_contra hnotIncident
  let edge : G.edgeSet := componentEdge.1.1
  have hedgeComponent : edge ∈ C.kempeComponentSet a b K := by
    exact ⟨componentEdge.1.2, componentEdge.2⟩
  have hendpointCubic : ∀ vertex ∈ (edge : Sym2 V),
      (incidentEdgeFinset G vertex).card = 3 := by
    intro vertex hvertex
    have hnotDefect : ∀ i : Fin 2, vertex ≠ data.defectVertex i := by
      intro i heq
      apply hnotIncident
      refine ⟨i, ?_⟩
      simpa [edge, incidentEdgeFinset, heq] using hvertex
    have hnotStub : vertex ∉ data.frozenInterfaceStubVertices := by
      intro hstub
      have hedgeFrozen : edge ∈ data.frozenInterfaceEdges :=
        (hdata.frozen_edge_iff_incident_stub edge).2
          ⟨vertex, hstub, by
            simpa [incidentEdgeFinset] using hvertex⟩
      exact (Set.disjoint_left.1 hfrozen) hedgeComponent
        (by simpa using hedgeFrozen)
    exact hdata.cubic_elsewhere vertex hnotDefect hnotStub
  apply hdegree
  rw [connectedComponent_neighborSet_ncard_eq_parent K componentEdge]
  simpa [edge] using bicoloredSubgraph_neighborSet_ncard_eq_two_of_endpoint_cubic
    C hC hab edge componentEdge.1.2 hendpointCubic

/-- A legal selected component that is not circuit-shaped must meet one of the
two degree-two trail defects. -/
theorem kempeComponentMeetsDefect_of_not_circuit
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {a b : Color} (hab : ValidColorPair a b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hfrozen : Disjoint (C.kempeComponentSet a b K)
      (data.frozenInterfaceEdges : Set G.edgeSet))
    (hnoncircuit : ¬IsCircuitKempeComponent C a b K) :
    KempeComponentMeetsDefect data C a b K := by
  have hends := kempeComponentEndsOnlyAtDefects_of_legal
    data hdata C hC hab K hfrozen
  rw [IsCircuitKempeComponent] at hnoncircuit
  push Not at hnoncircuit
  rcases hnoncircuit with ⟨componentEdge, hdegree⟩
  rcases hends componentEdge hdegree with ⟨i, hincident⟩
  exact ⟨i, componentEdge.1.1,
    ⟨componentEdge.1.2, componentEdge.2⟩, hincident⟩

/-- With a Tait coloring on a well-formed frame, the noncircuit residue is
exactly the defect-meeting residue.  This is the first structural content
behind the source phrase "defect-ending path"; it is stronger than merely
naming the complement of the circuit relation. -/
theorem noncircuitFramedKempeStep_iff_defectPathFramedKempeStep
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (C' : G.EdgeColoring Color) :
    NoncircuitFramedKempeStep data C C' ↔
      DefectPathFramedKempeStep data C C' := by
  constructor
  · rintro ⟨a, b, K, hab, hnoncircuit, hfrozen, hswap⟩
    have hends := kempeComponentEndsOnlyAtDefects_of_legal
      data hdata C hC hab K hfrozen
    exact ⟨a, b, K, hab, hnoncircuit, hends,
      kempeComponentMeetsDefect_of_not_circuit
        data hdata C hC hab K hfrozen hnoncircuit,
      hfrozen, hswap⟩
  · rintro ⟨a, b, K, hab, hnoncircuit, _hends, _hmeets,
      hfrozen, hswap⟩
    exact ⟨a, b, K, hab, hnoncircuit, hfrozen, hswap⟩

/-- Corrected graph-side L10 statement.  Under a certified identification of
the source annulus with the movable frame, framed moves are exactly the v23
circuit moves together with the defect-ending path moves forced by the repaired
degree-two semantics. -/
theorem framedTangleLegalKempeStep_iff_kauffman_or_defectPath
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (haligned : data.BetweenRegionEdgeAligned)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (C' : G.EdgeColoring Color) :
    FramedTangleLegalKempeStep data C C' ↔
      KauffmanBetweenRegionKempeStep data C C' ∨
        DefectPathFramedKempeStep data C C' := by
  rw [framedTangleLegalKempeStep_iff_kauffman_or_noncircuit
      hdata haligned,
    noncircuitFramedKempeStep_iff_defectPathFramedKempeStep
      data hdata C hC C']

/-- The source-faithful repaired one-step relation: the original annular
circuits plus the defect-ending paths required by the framed repair. -/
def SourceBetweenRegionKempeStep
    (data : FramedTrailData G)
    (C C' : G.EdgeColoring Color) : Prop :=
  KauffmanBetweenRegionKempeStep data C C' ∨
    DefectPathFramedKempeStep data C C'

/-- Finite reachability generated by the corrected source-side move family. -/
def SourceBetweenRegionKempeReachable
    (data : FramedTrailData G) :
    G.EdgeColoring Color → G.EdgeColoring Color → Prop :=
  Relation.ReflTransGen (SourceBetweenRegionKempeStep data)

/-- Corrected graph-side L10 at finite reachability.  The initial coloring is
Tait, and framed moves preserve that property, so the pointwise source/frame
identification propagates through every finite move sequence. -/
theorem sourceBetweenRegionKempeReachable_iff_framedTangleKempeReachable
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (haligned : data.BetweenRegionEdgeAligned)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (C' : G.EdgeColoring Color) :
    SourceBetweenRegionKempeReachable data C C' ↔
      FramedTangleKempeReachable data C C' := by
  constructor
  · intro hreach
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head hstep htail ih =>
        have hframedStep : FramedTangleLegalKempeStep data _ _ :=
          (framedTangleLegalKempeStep_iff_kauffman_or_defectPath
            data hdata haligned _ hC _).2 hstep
        have hnextTait :=
          framedTangleLegalKempeStep_preserves_isTaitEdgeColoring
            hframedStep hC
        exact .head hframedStep (ih hnextTait)
  · intro hreach
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head hstep htail ih =>
        have hsourceStep : SourceBetweenRegionKempeStep data _ _ :=
          (framedTangleLegalKempeStep_iff_kauffman_or_defectPath
            data hdata haligned _ hC _).1 hstep
        have hnextTait :=
          framedTangleLegalKempeStep_preserves_isTaitEdgeColoring hstep hC
        exact .head hsourceStep (ih hnextTait)

/-- Trail completion using the corrected source-side circuit/path move family. -/
def SourceBetweenRegionCompletable
    (data : FramedTrailData G) (C : G.EdgeColoring Color) : Prop :=
  ∃ C' : G.EdgeColoring Color,
    SourceBetweenRegionKempeReachable data C C' ∧
      data.HasMatchingDefectColors C'

/-- Corrected graph-side L10 at the completion predicate.  This is still
conditional on `BetweenRegionEdgeAligned`; constructing that alignment from
the formation/container embedding is the remaining source-geometric bridge. -/
theorem sourceBetweenRegionCompletable_iff_framedTangleCompletable
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (haligned : data.BetweenRegionEdgeAligned)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    SourceBetweenRegionCompletable data C ↔
      FramedTangleCompletable data C := by
  constructor
  · rintro ⟨C', hreach, hmatch⟩
    exact ⟨C',
      (sourceBetweenRegionKempeReachable_iff_framedTangleKempeReachable
        data hdata haligned C hC C').1 hreach,
      hmatch⟩
  · rintro ⟨C', hreach, hmatch⟩
    exact ⟨C',
      (sourceBetweenRegionKempeReachable_iff_framedTangleKempeReachable
        data hdata haligned C hC C').2 hreach,
      hmatch⟩

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
