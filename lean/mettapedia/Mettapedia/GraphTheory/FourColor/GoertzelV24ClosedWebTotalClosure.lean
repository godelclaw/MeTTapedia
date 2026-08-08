import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebComponentCensus

/-!
# Web Closure and Cubic Closure for the v24 annular tangle

This module formalizes the source definition rather than identifying total
closure with its desired consequence.

A *web edge* is an edge lying in an inner-touching component of one valid
Tait color pair.  A web is *totally closed* when, for every web edge, every
valid color-pair component containing that same edge is inner-touching.  This
is the manuscript's statement that every edge of every web strand has both
of its bichromatic components inner-touching; orientations are harmlessly
quantified twice.

Cubic propagation is then literal.  A web edge incident to a second ambient
edge determines the color pair formed by their two distinct nonzero colors.
Total closure makes that pair component inner-touching, so the second edge is
also web.  Connectivity propagates from one inner-boundary seed edge to every
ambient edge, yielding the source conclusion that every bichromatic strand
is inner-touching.  At five outer stubs this feeds the component census and
the two-radial-path theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebTotalClosure

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebSelectedEdgeStructure
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebInnerTouching
open GoertzelV24ClosedWebComponentCensus

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable local instance colorPairGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color) (vertex : V) :
    Fintype ((colorPairGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

noncomputable local instance colorPairSupportGraphNeighborSetFintype
    (C : G.EdgeColoring Color) (first second : Color)
    (vertex : ColorPairSupportVertex C first second) :
    Fintype ((colorPairSupportGraph C first second).neighborSet vertex) := by
  classical
  exact Subtype.fintype _

/-- An oriented ambient edge lies in an inner-touching bichromatic strand. -/
def IsWebEdge
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (left right : V) : Prop :=
  ∃ first second : Color,
    ValidColorPair first second ∧
    ∃ hadjacent : (colorPairGraph C first second).Adj left right,
      ∃ inner : Fin 5,
        ComponentContainsInnerStub data C first second
          ((colorPairSupportGraph C first second).connectedComponentMk
            ⟨left, hadjacent.mem_support_left⟩)
          inner

/-- Source-level total closure: every valid bichromatic component containing
an edge of an inner-touching web strand is itself inner-touching. -/
def TotallyClosedWeb
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) : Prop :=
  ∀ webFirst webSecond : Color,
    ValidColorPair webFirst webSecond →
    ∀ left right : V,
      ∀ webAdjacent :
        (colorPairGraph C webFirst webSecond).Adj left right,
      (∃ inner : Fin 5,
        ComponentContainsInnerStub data C webFirst webSecond
          ((colorPairSupportGraph C webFirst webSecond).connectedComponentMk
            ⟨left, webAdjacent.mem_support_left⟩)
          inner) →
      ∀ otherFirst otherSecond : Color,
        ValidColorPair otherFirst otherSecond →
        ∀ otherAdjacent :
          (colorPairGraph C otherFirst otherSecond).Adj left right,
          ∃ inner : Fin 5,
            ComponentContainsInnerStub data C otherFirst otherSecond
              ((colorPairSupportGraph C otherFirst otherSecond).connectedComponentMk
                ⟨left, otherAdjacent.mem_support_left⟩)
              inner

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Reversing an oriented web edge preserves its web status. -/
theorem isWebEdge_symm
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) {left right : V}
    (hweb : IsWebEdge data C left right) :
    IsWebEdge data C right left := by
  rcases hweb with
    ⟨first, second, hpair, hadjacent, inner, hinner⟩
  let leftVertex : ColorPairSupportVertex C first second :=
    ⟨left, hadjacent.mem_support_left⟩
  let rightVertex : ColorPairSupportVertex C first second :=
    ⟨right, hadjacent.mem_support_right⟩
  have hsupportAdjacent :
      (colorPairSupportGraph C first second).Adj leftVertex rightVertex := by
    simpa [colorPairSupportGraph, leftVertex, rightVertex] using hadjacent
  have hcomponents :
      (colorPairSupportGraph C first second).connectedComponentMk leftVertex =
        (colorPairSupportGraph C first second).connectedComponentMk rightVertex :=
    ConnectedComponent.connectedComponentMk_eq_of_adj hsupportAdjacent
  refine ⟨first, second, hpair, hadjacent.symm, inner, ?_⟩
  simpa [leftVertex, rightVertex, hcomponents] using hinner

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Total closure applied to one web edge and another selected pair on the
same edge. -/
theorem component_innerTouching_of_totallyClosed_of_isWebEdge
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color)
    (hclosed : TotallyClosedWeb data C)
    {left right : V} (hweb : IsWebEdge data C left right)
    {first second : Color} (hpair : ValidColorPair first second)
    (hadjacent : (colorPairGraph C first second).Adj left right) :
    ∃ inner : Fin 5,
      ComponentContainsInnerStub data C first second
        ((colorPairSupportGraph C first second).connectedComponentMk
          ⟨left, hadjacent.mem_support_left⟩)
        inner := by
  rcases hweb with
    ⟨webFirst, webSecond, hwebPair, hwebAdjacent, _inner, hwebInner⟩
  exact hclosed webFirst webSecond hwebPair left right hwebAdjacent
    ⟨_inner, hwebInner⟩ first second hpair hadjacent

omit [Fintype V] [DecidableRel G.Adj] in
/-- Cubic propagation in edge form: an ambient edge adjacent to a web edge
is itself a web edge.  Properness supplies distinct colors when the edges
are distinct; the coincident-edge case is symmetry. -/
theorem isWebEdge_of_isWebEdge_of_adjacent_edge
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hclosed : TotallyClosedWeb data C)
    {left middle right : V}
    (hweb : IsWebEdge data C left middle)
    (hadjacent : G.Adj middle right) :
    IsWebEdge data C middle right := by
  classical
  by_cases hrightLeft : right = left
  · subst right
    exact isWebEdge_symm data C hweb
  have hwebAtMiddle : IsWebEdge data C middle left :=
    isWebEdge_symm data C hweb
  rcases hwebAtMiddle with
    ⟨webFirst, webSecond, hwebPair, hwebAdjacent,
      webInner, hwebInner⟩
  have hwebAmbient : G.Adj middle left :=
    colorPairGraph_le C webFirst webSecond hwebAdjacent
  let webEdge : G.edgeSet :=
    ⟨s(middle, left), by simpa using hwebAmbient⟩
  let targetEdge : G.edgeSet :=
    ⟨s(middle, right), by simpa using hadjacent⟩
  have hedgesNe : webEdge ≠ targetEdge := by
    intro hedgesEq
    have hpairs : s(middle, left) = s(middle, right) :=
      congrArg Subtype.val hedgesEq
    rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
    · exact hrightLeft hstraight.2.symm
    · exact hadjacent.ne hswapped.1
  have hlineAdjacent : G.lineGraph.Adj webEdge targetEdge :=
    G.lineGraph_adj_of_edgeSet_common_vertex hedgesNe
      (Sym2.mem_mk_left middle left) (Sym2.mem_mk_left middle right)
  have hcolorsNe : C webEdge ≠ C targetEdge := C.valid hlineAdjacent
  have hnewPair : ValidColorPair (C webEdge) (C targetEdge) :=
    ⟨hC webEdge, hC targetEdge, hcolorsNe⟩
  have hwebSelected :
      (colorPairGraph C (C webEdge) (C targetEdge)).Adj middle left := by
    apply (colorPairGraph_adj_iff C (C webEdge) (C targetEdge)
      middle left).2
    exact ⟨hwebAmbient, Or.inl rfl⟩
  have htargetSelected :
      (colorPairGraph C (C webEdge) (C targetEdge)).Adj middle right := by
    apply (colorPairGraph_adj_iff C (C webEdge) (C targetEdge)
      middle right).2
    exact ⟨hadjacent, Or.inr rfl⟩
  have hnewInner :=
    hclosed webFirst webSecond hwebPair middle left hwebAdjacent
      ⟨webInner, hwebInner⟩ (C webEdge) (C targetEdge) hnewPair
      hwebSelected
  exact ⟨C webEdge, C targetEdge, hnewPair, htargetSelected, hnewInner⟩

/-- A vertex has at least one incident web edge. -/
def HasIncidentWebEdge
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (vertex : V) : Prop :=
  ∃ neighbor : V, IsWebEdge data C vertex neighbor

omit [Fintype V] [DecidableRel G.Adj] in
/-- Incident web-edge status propagates across an ambient edge. -/
theorem hasIncidentWebEdge_of_adjacent
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hclosed : TotallyClosedWeb data C)
    {left right : V} (hleft : HasIncidentWebEdge data C left)
    (hadjacent : G.Adj left right) :
    HasIncidentWebEdge data C right := by
  rcases hleft with ⟨neighbor, hweb⟩
  have htarget := isWebEdge_of_isWebEdge_of_adjacent_edge
    data C hC hclosed (isWebEdge_symm data C hweb) hadjacent
  exact ⟨left, isWebEdge_symm data C htarget⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- Propagate an incident web edge along any ambient walk. -/
theorem hasIncidentWebEdge_of_reachable
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hclosed : TotallyClosedWeb data C)
    {start finish : V} (hstart : HasIncidentWebEdge data C start)
    (hreachable : G.Reachable start finish) :
    HasIncidentWebEdge data C finish := by
  rcases hreachable with ⟨walk⟩
  exact SimpleGraph.Walk.concatRec
    (motive := fun walkStart walkFinish _walk =>
      HasIncidentWebEdge data C walkStart →
        HasIncidentWebEdge data C walkFinish)
    (fun hincident => hincident)
    (fun _path hadjacent ih hincident =>
      hasIncidentWebEdge_of_adjacent
        data C hC hclosed (ih hincident) hadjacent)
    walk hstart

/-- The inner boundary supplies an initial web edge in every Tait coloring. -/
theorem exists_incidentWebEdge_at_innerBoundary
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    HasIncidentWebEdge data C (data.innerStub 0) := by
  classical
  have hcolorNonzero := hC (data.innerBoundaryEdge 0)
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero
      (C (data.innerBoundaryEdge 0)) hcolorNonzero with
    hred | hblue | hpurple
  · let pair : TaitPairIndex := .redBlue
    have hselected : pair.Selects (C (data.innerBoundaryEdge 0)) := by
      exact Or.inl hred
    let endpoint : InnerEnd data C := ⟨pair, ⟨0, hselected⟩⟩
    let start := innerEndVertex data hdata C endpoint
    rcases (colorPairGraph C pair.firstColor pair.secondColor).mem_support.mp
        start.property with
      ⟨neighbor, hadjacent⟩
    refine ⟨neighbor, pair.firstColor, pair.secondColor, pair.valid,
      hadjacent, 0, ?_⟩
    exact ⟨start, ConnectedComponent.connectedComponentMk_mem, rfl⟩
  · let pair : TaitPairIndex := .redBlue
    have hselected : pair.Selects (C (data.innerBoundaryEdge 0)) := by
      exact Or.inr hblue
    let endpoint : InnerEnd data C := ⟨pair, ⟨0, hselected⟩⟩
    let start := innerEndVertex data hdata C endpoint
    rcases (colorPairGraph C pair.firstColor pair.secondColor).mem_support.mp
        start.property with
      ⟨neighbor, hadjacent⟩
    refine ⟨neighbor, pair.firstColor, pair.secondColor, pair.valid,
      hadjacent, 0, ?_⟩
    exact ⟨start, ConnectedComponent.connectedComponentMk_mem, rfl⟩
  · let pair : TaitPairIndex := .redPurple
    have hselected : pair.Selects (C (data.innerBoundaryEdge 0)) := by
      exact Or.inr hpurple
    let endpoint : InnerEnd data C := ⟨pair, ⟨0, hselected⟩⟩
    let start := innerEndVertex data hdata C endpoint
    rcases (colorPairGraph C pair.firstColor pair.secondColor).mem_support.mp
        start.property with
      ⟨neighbor, hadjacent⟩
    refine ⟨neighbor, pair.firstColor, pair.secondColor, pair.valid,
      hadjacent, 0, ?_⟩
    exact ⟨start, ConnectedComponent.connectedComponentMk_mem, rfl⟩

/-- Cubic Closure, edge form: in a connected annular tangle, total closure
propagates from the inner-boundary seed to every ambient edge. -/
theorem every_edge_isWebEdge_of_totallyClosed
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (hconnected : G.Connected)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hclosed : TotallyClosedWeb data C)
    {left right : V} (hadjacent : G.Adj left right) :
    IsWebEdge data C left right := by
  have hseed := exists_incidentWebEdge_at_innerBoundary data hdata C hC
  have hleft := hasIncidentWebEdge_of_reachable
    data C hC hclosed hseed (hconnected (data.innerStub 0) left)
  rcases hleft with ⟨neighbor, hweb⟩
  exact isWebEdge_of_isWebEdge_of_adjacent_edge
    data C hC hclosed (isWebEdge_symm data C hweb) hadjacent

/-- Cubic Closure, component form: every bichromatic strand in a connected
totally closed annular web is inner-touching. -/
theorem everyColorPairComponentInnerTouching_of_totallyClosed
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (hconnected : G.Connected)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hclosed : TotallyClosedWeb data C) :
    EveryColorPairComponentInnerTouching data C := by
  intro first second hpair component
  rcases component.nonempty_supp with ⟨vertex, hvertexComponent⟩
  rcases (colorPairGraph C first second).mem_support.mp vertex.property with
    ⟨neighbor, hadjacent⟩
  have hambient : G.Adj vertex.1 neighbor :=
    colorPairGraph_le C first second hadjacent
  have hweb : IsWebEdge data C vertex.1 neighbor :=
    every_edge_isWebEdge_of_totallyClosed
      data hdata hconnected C hC hclosed hambient
  rcases component_innerTouching_of_totallyClosed_of_isWebEdge
      data C hclosed hweb hpair hadjacent with
    ⟨inner, hinner⟩
  have hcomponentEq :
      (colorPairSupportGraph C first second).connectedComponentMk vertex =
        component :=
    (ConnectedComponent.mem_supp_iff component vertex).mp hvertexComponent
  exact ⟨inner, by simpa [hcomponentEq] using hinner⟩

/-- Source-facing closure conclusion at the sharp five-stub boundary: total
closure plus connectivity and a good word force the singleton pair into two
radial paths covering its selected support. -/
theorem exists_singletonPair_two_radialPaths_at_five_of_totallyClosed
    (data : AnnularBoundaryData G 5) (hdata : data.WellFormed)
    (hconnected : G.Connected)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hclosed : TotallyClosedWeb data C)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord C)) :
    ∃ majority singletonFirst singletonSecond : Color,
      IsTaitColorTriple majority singletonFirst singletonSecond ∧
      ∃ firstComponent secondComponent :
          (colorPairSupportGraph C singletonFirst singletonSecond).ConnectedComponent,
        firstComponent ≠ secondComponent ∧
        ∃ firstPath : ComponentRadialPath
            data C singletonFirst singletonSecond firstComponent,
          ∃ secondPath : ComponentRadialPath
              data C singletonFirst singletonSecond secondComponent,
            firstPath.path.toSubgraph.verts ∪
                secondPath.path.toSubgraph.verts = Set.univ := by
  exact exists_singletonPair_two_radialPaths_at_five_of_goodWord_of_innerTouching
    data hdata C hC hgood
      (everyColorPairComponentInnerTouching_of_totallyClosed
        data hdata hconnected C hC hclosed)

end GoertzelV24ClosedWebTotalClosure

end Mettapedia.GraphTheory.FourColor
