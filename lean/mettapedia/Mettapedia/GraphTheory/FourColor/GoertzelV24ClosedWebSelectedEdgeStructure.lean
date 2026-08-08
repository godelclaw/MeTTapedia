import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalExactness

/-!
# Selected-edge structure for the v24 closed web

This module packages the global graph objects selected by one or two Tait
colors.  A single color class is a matching in the original graph.  The union
of two distinct color classes alternates between those classes at every pair
of consecutive edges.

Together with `GoertzelV24ClosedWebLocalExactness`, these are the precise
graph-theoretic ingredients behind the manuscript's phrases "chord matching"
and "alternating B-paths".  No claim is made here about the number, radiality,
or planar sector placement of the resulting components.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebSelectedEdgeStructure

open SimpleGraph
open GoertzelV24ClosedWebLocalExactness
open GoertzelV24FramedTrail
open GoertzelV24FramedBoundaryCounts

variable {V : Type*} {G : SimpleGraph V}

/-- The primal graph consisting of the edges carrying one selected color. -/
def colorClassGraph (C : G.EdgeColoring Color) (color : Color) : SimpleGraph V :=
  EdgeLabeling.labelGraph (fun edge : G.edgeSet => C edge) color

/-- The primal graph consisting of edges carrying either selected color. -/
def colorPairGraph (C : G.EdgeColoring Color) (first second : Color) :
    SimpleGraph V :=
  colorClassGraph C first ⊔ colorClassGraph C second

theorem colorClassGraph_adj_iff
    (C : G.EdgeColoring Color) (color : Color) (first second : V) :
    (colorClassGraph C color).Adj first second ↔
      ∃ h : G.Adj first second,
        C ⟨s(first, second), by simpa using h⟩ = color := by
  exact EdgeLabeling.labelGraph_adj first second

theorem colorPairGraph_adj_iff
    (C : G.EdgeColoring Color) (firstColor secondColor : Color)
    (firstVertex secondVertex : V) :
    (colorPairGraph C firstColor secondColor).Adj firstVertex secondVertex ↔
      ∃ h : G.Adj firstVertex secondVertex,
        C ⟨s(firstVertex, secondVertex), by simpa using h⟩ = firstColor ∨
        C ⟨s(firstVertex, secondVertex), by simpa using h⟩ = secondColor := by
  rw [colorPairGraph, sup_adj]
  simp only [colorClassGraph_adj_iff]
  constructor
  · rintro (⟨h, hcolor⟩ | ⟨h, hcolor⟩)
    · exact ⟨h, Or.inl hcolor⟩
    · exact ⟨h, Or.inr hcolor⟩
  · rintro ⟨h, hcolor | hcolor⟩
    · exact Or.inl ⟨h, hcolor⟩
    · exact Or.inr ⟨h, hcolor⟩

/-- Every selected monochromatic edge remains an edge of the ambient graph. -/
theorem colorClassGraph_le
    (C : G.EdgeColoring Color) (color : Color) :
    colorClassGraph C color ≤ G := by
  exact EdgeLabeling.labelGraph_le (fun edge : G.edgeSet => C edge)

/-- Every selected bichromatic edge remains an edge of the ambient graph. -/
theorem colorPairGraph_le
    (C : G.EdgeColoring Color) (first second : Color) :
    colorPairGraph C first second ≤ G := by
  rw [colorPairGraph, sup_le_iff]
  exact ⟨colorClassGraph_le C first, colorClassGraph_le C second⟩

/-- Regard a graph `H ≤ G` as the subgraph of `G` containing precisely the
support vertices and edges of `H`. -/
def supportedSubgraphOfLE (H : SimpleGraph V) (hHG : H ≤ G) : G.Subgraph where
  verts := H.support
  Adj := H.Adj
  adj_sub := fun hadj => hHG hadj
  edge_vert := fun hadj => hadj.mem_support_left
  symm := H.symm

/-- The ambient subgraph carried by one color class. -/
def colorClassSubgraph (C : G.EdgeColoring Color) (color : Color) : G.Subgraph :=
  supportedSubgraphOfLE (colorClassGraph C color) (colorClassGraph_le C color)

@[simp] theorem colorClassSubgraph_verts
    (C : G.EdgeColoring Color) (color : Color) :
    (colorClassSubgraph C color).verts = (colorClassGraph C color).support :=
  by simp [colorClassSubgraph, supportedSubgraphOfLE]

@[simp] theorem colorClassSubgraph_adj
    (C : G.EdgeColoring Color) (color : Color) (first second : V) :
    (colorClassSubgraph C color).Adj first second ↔
      (colorClassGraph C color).Adj first second :=
  by simp [colorClassSubgraph, supportedSubgraphOfLE]

/-- Properness makes the neighbor selected by a fixed color unique. -/
theorem colorClassGraph_existsUnique_adj
    (C : G.EdgeColoring Color) (color : Color)
    {vertex : V} (hvertex : vertex ∈ (colorClassGraph C color).support) :
    ∃! neighbor : V, (colorClassGraph C color).Adj vertex neighbor := by
  rcases (colorClassGraph C color).mem_support.mp hvertex with
    ⟨chosen, hchosen⟩
  refine ⟨chosen, hchosen, ?_⟩
  intro neighbor hneighbor
  rcases (colorClassGraph_adj_iff C color vertex chosen).1 hchosen with
    ⟨hchosenAmbient, hchosenColor⟩
  rcases (colorClassGraph_adj_iff C color vertex neighbor).1 hneighbor with
    ⟨hneighborAmbient, hneighborColor⟩
  by_contra hneighborChosen
  let chosenEdge : G.edgeSet :=
    ⟨s(vertex, chosen), by simpa using hchosenAmbient⟩
  let neighborEdge : G.edgeSet :=
    ⟨s(vertex, neighbor), by simpa using hneighborAmbient⟩
  have hedgesNe : chosenEdge ≠ neighborEdge := by
    intro hedgesEq
    have hpairs : s(vertex, chosen) = s(vertex, neighbor) :=
      congrArg Subtype.val hedgesEq
    rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
    · exact hneighborChosen hstraight.2.symm
    · exact hneighborAmbient.ne hswapped.1
  have hchosenAt : vertex ∈ (chosenEdge : Sym2 V) := by
    simp [chosenEdge]
  have hneighborAt : vertex ∈ (neighborEdge : Sym2 V) := by
    simp [neighborEdge]
  have hadjacent : G.lineGraph.Adj chosenEdge neighborEdge :=
    G.lineGraph_adj_of_edgeSet_common_vertex hedgesNe hchosenAt hneighborAt
  apply C.valid hadjacent
  change C chosenEdge = C neighborEdge
  exact hchosenColor.trans hneighborColor.symm

/-- A single Tait color class is a matching in the standard Mathlib sense. -/
theorem colorClassSubgraph_isMatching
    (C : G.EdgeColoring Color) (color : Color) :
    (colorClassSubgraph C color).IsMatching := by
  intro vertex hvertex
  apply colorClassGraph_existsUnique_adj C color
  simpa [colorClassSubgraph, supportedSubgraphOfLE] using hvertex

/-- The graph selected by two distinct Tait colors alternates between its two
monochromatic matchings. -/
theorem colorPairGraph_isAlternating_first
    (C : G.EdgeColoring Color) (first second : Color) :
    (colorPairGraph C first second).IsAlternating (colorClassGraph C first) := by
  intro vertex left right hleftRight hleft hright
  rcases (colorPairGraph_adj_iff C first second vertex left).1 hleft with
    ⟨hleftAmbient, hleftColor⟩
  rcases (colorPairGraph_adj_iff C first second vertex right).1 hright with
    ⟨hrightAmbient, hrightColor⟩
  let leftEdge : G.edgeSet :=
    ⟨s(vertex, left), by simpa using hleftAmbient⟩
  let rightEdge : G.edgeSet :=
    ⟨s(vertex, right), by simpa using hrightAmbient⟩
  have hleftEdgeNeRightEdge : leftEdge ≠ rightEdge := by
    intro hedge
    have hpairs : s(vertex, left) = s(vertex, right) :=
      congrArg Subtype.val hedge
    rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
    · exact hleftRight hstraight.2
    · exact hrightAmbient.ne hswapped.1
  have hcolorsNe : C leftEdge ≠ C rightEdge := by
    apply C.valid
    apply G.lineGraph_adj_of_edgeSet_common_vertex hleftEdgeNeRightEdge
    · exact Sym2.mem_mk_left vertex left
    · exact Sym2.mem_mk_left vertex right
  rw [colorClassGraph_adj_iff, colorClassGraph_adj_iff]
  constructor
  · rintro ⟨_hleftAmbient, hleftFirst⟩ ⟨_hrightAmbient, hrightFirst⟩
    apply hcolorsNe
    exact hleftFirst.trans hrightFirst.symm
  · intro hrightNotFirst
    refine ⟨hleftAmbient, ?_⟩
    rcases hleftColor with hleftFirst | hleftSecond
    · exact hleftFirst
    · rcases hrightColor with hrightFirst | hrightSecond
      · exact False.elim (hrightNotFirst ⟨hrightAmbient, hrightFirst⟩)
      · apply False.elim
        apply hcolorsNe
        exact hleftSecond.trans hrightSecond.symm

/-- The same bichromatic graph also alternates relative to the other color
class. -/
theorem colorPairGraph_isAlternating_second
    (C : G.EdgeColoring Color) (first second : Color) :
    (colorPairGraph C first second).IsAlternating (colorClassGraph C second) := by
  simpa [colorPairGraph, sup_comm] using
    colorPairGraph_isAlternating_first C second first

section FiniteIncidence

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  [Fintype G.edgeSet]

noncomputable local instance colorPairGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V) :
    Fintype ((colorPairGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

/-- The incidence finset in the selected primal graph is exactly the image of
the filtered ambient incident-edge finset. -/
theorem colorPairGraph_incidenceFinset_eq_map_incidentEdges
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V) :
    (colorPairGraph C first second).incidenceFinset vertex =
      (incidentEdgesOfColorPair C first second vertex).map
        (Function.Embedding.subtype
          (fun edge : Sym2 V => edge ∈ G.edgeSet)) := by
  ext edge
  induction edge using Sym2.inductionOn with
  | _ left right =>
      simp [SimpleGraph.incidenceFinset_eq_filter, colorPairGraph,
        colorClassGraph, incidentEdgesOfColorPair, incidentEdgeFinset,
        SimpleGraph.mem_edgeSet, EdgeLabeling.labelGraph_adj]
      aesop

/-- Degree in the selected primal graph is the cardinality already computed
by the local filtered-edge API. -/
theorem colorPairGraph_degree_eq_card_incidentEdges
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V) :
    (colorPairGraph C first second).degree vertex =
      (incidentEdgesOfColorPair C first second vertex).card := by
  calc
    (colorPairGraph C first second).degree vertex =
        ((colorPairGraph C first second).incidenceFinset vertex).card := by
      exact ((colorPairGraph C first second).card_incidenceFinset_eq_degree vertex).symm
    _ = (incidentEdgesOfColorPair C first second vertex).card := by
      rw [colorPairGraph_incidenceFinset_eq_map_incidentEdges]
      simp

/-- The selected `B₁/B₂` primal graph has degree exactly two at a cubic Tait
vertex. -/
theorem colorPairGraph_degree_eq_two_of_cubic_tait
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (vertex : V) (hcubic : (incidentEdgeFinset G vertex).card = 3)
    {first second : Color} (hpair : ValidColorPair first second) :
    (colorPairGraph C first second).degree vertex = 2 := by
  rw [colorPairGraph_degree_eq_card_incidentEdges]
  exact incidentEdgesOfColorPair_card_eq_two_of_cubic_tait
    C hC vertex hcubic hpair

/-- In the framed source model, every cubic interior vertex has selected
`B₁/B₂` degree exactly two. -/
theorem cubicInterior_colorPairGraph_degree_eq_two
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {vertex : V} (hvertex : vertex ∈ cubicInteriorVertices data)
    {first second : Color} (hpair : ValidColorPair first second) :
    (colorPairGraph C first second).degree vertex = 2 := by
  exact colorPairGraph_degree_eq_two_of_cubic_tait C hC vertex
    (cubicInterior_incidentEdgeFinset_card_eq_three data hdata hvertex)
    hpair

end FiniteIncidence

end GoertzelV24ClosedWebSelectedEdgeStructure

end Mettapedia.GraphTheory.FourColor
