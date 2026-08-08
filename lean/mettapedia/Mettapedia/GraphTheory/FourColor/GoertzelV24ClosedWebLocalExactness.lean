import Mettapedia.GraphTheory.FourColor.GoertzelV24BetweenRegionDefectPaths
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCounts

/-!
# Local exactness for the v24 closed-web decomposition

This is the local graph-theoretic input to the manuscript's
`B₁ ∪ B₂ ∪ α` exact system.  At every cubic interior vertex of a framed
Tait-colored graph, a selected color occurs on exactly one incident edge,
while a selected pair of colors occurs on exactly two incident edges.  For a
valid pair `B₁, B₂`, those two edges together with the unique third-color
`α = B₁ + B₂` edge partition the three incident edges.

No global path, chord, laminarity, or sector-alternation conclusion is claimed
here.  Those require the remaining planar closed-web structure from the
source proof.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalExactness

open SimpleGraph
open GoertzelV24FramedTrail
open GoertzelV24FramedBoundaryCounts

variable {V : Type*} [DecidableEq V]
  {G : SimpleGraph V} [Fintype G.edgeSet]

/-- Incident edges carrying one specified Tait color. -/
def incidentEdgesOfColor (C : G.EdgeColoring Color) (color : Color)
    (vertex : V) : Finset G.edgeSet :=
  (incidentEdgeFinset G vertex).filter fun edge => C edge = color

@[simp] theorem mem_incidentEdgesOfColor_iff
    (C : G.EdgeColoring Color) (color : Color) (vertex : V)
    (edge : G.edgeSet) :
    edge ∈ incidentEdgesOfColor C color vertex ↔
      edge ∈ incidentEdgeFinset G vertex ∧ C edge = color := by
  simp [incidentEdgesOfColor]

/-- Incident edges carrying either member of a specified Tait-color pair. -/
def incidentEdgesOfColorPair (C : G.EdgeColoring Color) (first second : Color)
    (vertex : V) : Finset G.edgeSet :=
  (incidentEdgeFinset G vertex).filter fun edge =>
    C edge = first ∨ C edge = second

@[simp] theorem mem_incidentEdgesOfColorPair_iff
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V)
    (edge : G.edgeSet) :
    edge ∈ incidentEdgesOfColorPair C first second vertex ↔
      edge ∈ incidentEdgeFinset G vertex ∧
        (C edge = first ∨ C edge = second) := by
  simp [incidentEdgesOfColorPair]

/-- Distinct colors select disjoint sets of incident edges. -/
theorem incidentEdgesOfColor_disjoint
    (C : G.EdgeColoring Color) (vertex : V)
    {first second : Color} (hne : first ≠ second) :
    Disjoint (incidentEdgesOfColor C first vertex)
      (incidentEdgesOfColor C second vertex) := by
  rw [Finset.disjoint_left]
  intro edge hfirst hsecond
  have hfirstColor := (mem_incidentEdgesOfColor_iff C first vertex edge).1 hfirst
  have hsecondColor :=
    (mem_incidentEdgesOfColor_iff C second vertex edge).1 hsecond
  exact hne (hfirstColor.2.symm.trans hsecondColor.2)

/-- Selecting a pair of colors is the union of the two monochromatic
incident-edge sets. -/
theorem incidentEdgesOfColorPair_eq_union
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V) :
    incidentEdgesOfColorPair C first second vertex =
      incidentEdgesOfColor C first vertex ∪
        incidentEdgesOfColor C second vertex := by
  ext edge
  simp only [mem_incidentEdgesOfColorPair_iff,
    Finset.mem_union, mem_incidentEdgesOfColor_iff]
  constructor
  · rintro ⟨hincident, hfirst | hsecond⟩
    · exact Or.inl ⟨hincident, hfirst⟩
    · exact Or.inr ⟨hincident, hsecond⟩
  · rintro (⟨hincident, hfirst⟩ | ⟨hincident, hsecond⟩)
    · exact ⟨hincident, Or.inl hfirst⟩
    · exact ⟨hincident, Or.inr hsecond⟩

/-- At a cubic Tait vertex, each nonzero color occurs exactly once. -/
theorem incidentEdgesOfColor_card_eq_one_of_cubic_tait
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (vertex : V) (hcubic : (incidentEdgeFinset G vertex).card = 3)
    (color : Color) (hcolor : color ≠ 0) :
    (incidentEdgesOfColor C color vertex).card = 1 := by
  rcases exists_incident_edge_of_color_of_cubic_tait
      C hC vertex hcubic color hcolor with ⟨chosen, hchosen, hchosenColor⟩
  apply Finset.card_eq_one.mpr
  refine ⟨chosen, ?_⟩
  ext edge
  constructor
  · intro hedge
    have hedgeData :=
      (mem_incidentEdgesOfColor_iff C color vertex edge).1 hedge
    apply Finset.mem_singleton.mpr
    by_contra hne
    have hedgeAt : vertex ∈ (edge : Sym2 V) := by
      simpa [incidentEdgeFinset] using hedgeData.1
    have hchosenAt : vertex ∈ (chosen : Sym2 V) := by
      simpa [incidentEdgeFinset] using hchosen
    exact C.valid
      (G.lineGraph_adj_of_edgeSet_common_vertex hne hedgeAt hchosenAt)
      (hedgeData.2.trans hchosenColor.symm)
  · intro hedge
    have hedgeEq : edge = chosen := Finset.mem_singleton.mp hedge
    subst edge
    exact (mem_incidentEdgesOfColor_iff C color vertex chosen).2
      ⟨hchosen, hchosenColor⟩

/-- At a cubic Tait vertex, two distinct nonzero colors occur on exactly two
incident edges. -/
theorem incidentEdgesOfColorPair_card_eq_two_of_cubic_tait
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (vertex : V) (hcubic : (incidentEdgeFinset G vertex).card = 3)
    {first second : Color} (hpair : ValidColorPair first second) :
    (incidentEdgesOfColorPair C first second vertex).card = 2 := by
  rw [incidentEdgesOfColorPair_eq_union]
  rw [Finset.card_union_of_disjoint
    (incidentEdgesOfColor_disjoint C vertex hpair.2.2)]
  rw [incidentEdgesOfColor_card_eq_one_of_cubic_tait
      C hC vertex hcubic first hpair.1,
    incidentEdgesOfColor_card_eq_one_of_cubic_tait
      C hC vertex hcubic second hpair.2.1]

/-- The `B₁`, `B₂`, and third-color `α` selections partition all three edges
at a cubic Tait vertex. -/
theorem incidentEdges_pair_union_third_eq_all_of_cubic_tait
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (vertex : V) (hcubic : (incidentEdgeFinset G vertex).card = 3)
    {first second : Color} (hpair : ValidColorPair first second) :
    incidentEdgesOfColorPair C first second vertex ∪
        incidentEdgesOfColor C (first + second) vertex =
      incidentEdgeFinset G vertex := by
  have hthird := third_color_properties hpair.1 hpair.2.1 hpair.2.2
  have hdisjoint :
      Disjoint (incidentEdgesOfColorPair C first second vertex)
        (incidentEdgesOfColor C (first + second) vertex) := by
    rw [incidentEdgesOfColorPair_eq_union]
    exact Finset.disjoint_union_left.mpr
      ⟨incidentEdgesOfColor_disjoint C vertex hthird.2.1.symm,
        incidentEdgesOfColor_disjoint C vertex hthird.2.2.symm⟩
  have hsubset :
      incidentEdgesOfColorPair C first second vertex ∪
          incidentEdgesOfColor C (first + second) vertex ⊆
        incidentEdgeFinset G vertex := by
    intro edge hedge
    rcases Finset.mem_union.mp hedge with hselected | hthirdEdge
    · exact (mem_incidentEdgesOfColorPair_iff
        C first second vertex edge).1 hselected |>.1
    · exact (mem_incidentEdgesOfColor_iff
        C (first + second) vertex edge).1 hthirdEdge |>.1
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [Finset.card_union_of_disjoint hdisjoint,
    incidentEdgesOfColorPair_card_eq_two_of_cubic_tait
      C hC vertex hcubic hpair,
    incidentEdgesOfColor_card_eq_one_of_cubic_tait
      C hC vertex hcubic (first + second) hthird.1,
    hcubic]

/-- Membership in the framed graph's interior class supplies the exact cubic
incidence hypothesis needed by the local closed-web calculation. -/
theorem cubicInterior_incidentEdgeFinset_card_eq_three
    [Fintype V]
    (data : FramedTrailData G) (hdata : data.WellFormed)
    {vertex : V} (hvertex : vertex ∈ cubicInteriorVertices data) :
    (incidentEdgeFinset G vertex).card = 3 := by
  have hnotBoundary := (Finset.mem_sdiff.mp hvertex).2
  apply hdata.cubic_elsewhere vertex
  · intro index
    fin_cases index
    · intro heq
      apply hnotBoundary
      exact Finset.mem_union_left _ (by simp [defectVertices, heq])
    · intro heq
      apply hnotBoundary
      exact Finset.mem_union_left _ (by simp [defectVertices, heq])
  · intro hstub
    apply hnotBoundary
    exact Finset.mem_union_right _ hstub

/-- Source-level local closed-web exactness: each framed cubic interior
vertex has exactly two `B₁/B₂` edges, exactly one `α = B₁ + B₂` edge, and
these three edges exhaust its incidence. -/
theorem cubicInterior_closedWeb_local_exactness
    [Fintype V]
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {vertex : V} (hvertex : vertex ∈ cubicInteriorVertices data)
    {first second : Color} (hpair : ValidColorPair first second) :
    (incidentEdgesOfColorPair C first second vertex).card = 2 ∧
      (incidentEdgesOfColor C (first + second) vertex).card = 1 ∧
      incidentEdgesOfColorPair C first second vertex ∪
          incidentEdgesOfColor C (first + second) vertex =
        incidentEdgeFinset G vertex := by
  have hcubic :=
    cubicInterior_incidentEdgeFinset_card_eq_three data hdata hvertex
  have hthird := third_color_properties hpair.1 hpair.2.1 hpair.2.2
  exact ⟨incidentEdgesOfColorPair_card_eq_two_of_cubic_tait
      C hC vertex hcubic hpair,
    incidentEdgesOfColor_card_eq_one_of_cubic_tait
      C hC vertex hcubic (first + second) hthird.1,
    incidentEdges_pair_union_third_eq_all_of_cubic_tait
      C hC vertex hcubic hpair⟩

end GoertzelV24ClosedWebLocalExactness

end Mettapedia.GraphTheory.FourColor
