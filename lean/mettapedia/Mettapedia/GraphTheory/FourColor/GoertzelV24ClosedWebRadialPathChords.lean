import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialComponents
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFaceTracing
import Mettapedia.GraphTheory.PathChord

/-!
# Same-path chords on the v24 closed-web radial paths

The closed-web component census produces paths in an induced two-color
support graph.  The Sector-Alternation argument, however, speaks about those
paths and the remaining-color chords in the ambient cubic graph.  This module
provides that exact bridge without adding a geometric conclusion.

In particular, a `MajorityChordOnRadialPath` is data already present in the
source picture: two ordered positions on one radial path joined by an ambient
edge of the third Tait color.  Its boundary theorem packages the chord and the
intervening path interval as the primal wall expected by the finite face trace.
No assertion is made here that the wall bounds a hole-free region or that two
such chords cannot nest.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebRadialPathChords

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebSelectedEdgeStructure

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Inclusion of a selected color-pair support graph into the ambient graph. -/
def colorPairSupportToAmbientHom
    (C : G.EdgeColoring Color) (first second : Color) :
    colorPairSupportGraph C first second →g G where
  toFun := Subtype.val
  map_rel' := by
    intro left right hadjacent
    exact colorPairGraph_le C first second hadjacent

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The component path, viewed as a walk in the ambient cubic graph. -/
def ambientRadialPath
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    G.Walk radial.start.1 radial.finish.1 :=
  radial.path.map (colorPairSupportToAmbientHom C first second)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem ambientRadialPath_length
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    (ambientRadialPath radial).length = radial.path.length := by
  unfold ambientRadialPath
  exact radial.path.length_map (colorPairSupportToAmbientHom C first second)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem ambientRadialPath_getVert
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (position : Nat) :
    (ambientRadialPath radial).getVert position =
      (radial.path.getVert position).1 := by
  unfold ambientRadialPath
  exact radial.path.getVert_map
    (colorPairSupportToAmbientHom C first second) position

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The ambient realization retains the simplicity of the support path. -/
theorem ambientRadialPath_isPath
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    (ambientRadialPath radial).IsPath := by
  exact SimpleGraph.Walk.map_isPath_of_injective
    (f := colorPairSupportToAmbientHom C first second)
    Subtype.val_injective radial.path_isPath

/-- The first ambient radial-path dart lies over its named inner boundary
edge. -/
theorem ambientRadialPath_firstDart_edgeOf_eq_innerBoundaryEdge
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (hnil : ¬(ambientRadialPath radial).Nil) :
    ((ambientRadialPath radial).firstDart hnil).edge =
      (data.innerBoundaryEdge radial.inner).1 := by
  have hmem :
      (⟨((ambientRadialPath radial).firstDart hnil).edge,
        ((ambientRadialPath radial).firstDart hnil).edge_mem⟩ : G.edgeSet) ∈
        incidentEdgeFinset G (data.innerStub radial.inner) := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [← radial.start_eq_innerStub]
    simp [SimpleGraph.Dart.edge]
  rw [data.innerStub_incidentEdgeFinset_eq_singleton hdata] at hmem
  simpa using congrArg Subtype.val (Finset.mem_singleton.mp hmem)

/-- The last ambient radial-path dart lies over its named outer boundary
edge. -/
theorem ambientRadialPath_lastDart_edgeOf_eq_outerBoundaryEdge
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (hnil : ¬(ambientRadialPath radial).Nil) :
    ((ambientRadialPath radial).lastDart hnil).edge =
      (data.outerBoundaryEdge radial.outer).1 := by
  have hmem :
      (⟨((ambientRadialPath radial).lastDart hnil).edge,
        ((ambientRadialPath radial).lastDart hnil).edge_mem⟩ : G.edgeSet) ∈
        incidentEdgeFinset G (data.outerStub radial.outer) := by
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [← radial.finish_eq_outerStub]
    simp [SimpleGraph.Dart.edge]
  rw [data.outerStub_incidentEdgeFinset_eq_singleton hdata] at hmem
  simpa using congrArg Subtype.val (Finset.mem_singleton.mp hmem)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Vertex positions on a radial path are injective through the final
position. -/
theorem ambientRadialPath_getVert_injective
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    Function.Injective (fun position : Fin (radial.path.length + 1) =>
      (ambientRadialPath radial).getVert position) := by
  intro left right heq
  apply Fin.ext
  apply (ambientRadialPath_isPath radial).getVert_injOn
  · simpa [ambientRadialPath_length] using Nat.le_of_lt_succ left.isLt
  · simpa [ambientRadialPath_length] using Nat.le_of_lt_succ right.isLt
  · exact heq

/-- Every strict interior position of a radial path is an interior vertex of
the annular tangle and therefore has exactly three incident ambient edges.
The proof uses the two distinct path neighbors to exclude all degree-one
boundary stubs. -/
theorem ambientRadialPath_internal_incidentEdgeFinset_card_eq_three
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (position : Nat) (hpositive : position ≠ 0)
    (hbeforeEnd : position < radial.path.length) :
    (incidentEdgeFinset G
      ((ambientRadialPath radial).getVert position)).card = 3 := by
  let path := ambientRadialPath radial
  let vertex := path.getVert position
  have hpath : path.IsPath := ambientRadialPath_isPath radial
  have hpathNeighborCount :
      (path.toSubgraph.neighborSet vertex).ncard = 2 := by
    exact hpath.ncard_neighborSet_toSubgraph_internal_eq_two
      hpositive (by simpa [path, ambientRadialPath_length] using hbeforeEnd)
  have hneighborSubset :
      path.toSubgraph.neighborSet vertex ⊆ G.neighborSet vertex := by
    intro neighbor hneighbor
    exact path.toSubgraph.adj_sub hneighbor
  have hdegreeAtLeastTwo : 2 ≤ G.degree vertex := by
    have hsubsetCard := Set.ncard_le_ncard hneighborSubset
    have hambientNeighborCount :
        (G.neighborSet vertex).ncard = G.degree vertex := by
      simpa only [Set.fintypeCard_eq_ncard] using
        (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := vertex))
    omega
  apply hdata.cubic_elsewhere vertex
  · intro inner heq
    have hdegreeOne : G.degree vertex = 1 := by
      rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree]
      simpa [heq] using hdata.inner_stub_degree_one inner
    omega
  · intro outer heq
    have hdegreeOne : G.degree vertex = 1 := by
      rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree]
      simpa [heq] using hdata.outer_stub_degree_one outer
    omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The ambient edge traversed at one position of a radial path. -/
def ambientRadialPathStepEdge
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (position : Nat) (hposition : position < radial.path.length) :
    G.edgeSet :=
  ⟨s((ambientRadialPath radial).getVert position,
      (ambientRadialPath radial).getVert (position + 1)), by
    apply (ambientRadialPath radial).adj_getVert_succ
    simpa using hposition⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every step of the ambient radial path still has one of the two selected
colors. -/
theorem ambientRadialPath_step_color
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (position : Nat) (hposition : position < radial.path.length) :
    C (ambientRadialPathStepEdge radial position hposition) = first ∨
      C (ambientRadialPathStepEdge radial position hposition) = second := by
  have hsupport := radial.path.adj_getVert_succ hposition
  change (colorPairGraph C first second).Adj
    (radial.path.getVert position).1
    (radial.path.getVert (position + 1)).1 at hsupport
  rcases (colorPairGraph_adj_iff C first second _ _).1 hsupport with
    ⟨_hambient, hcolor⟩
  simpa [ambientRadialPathStepEdge] using hcolor

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every ambient edge traversed by a selected color-pair walk retains one of
the two selected colors.  This is the edge-level form needed when a chord
cycle is inspected at an interior path position. -/
theorem mapped_walk_edges_color_pair
    {C : G.EdgeColoring Color} {first second : Color}
    {start finish : ColorPairSupportVertex C first second}
    (walk : (colorPairSupportGraph C first second).Walk start finish)
    (edge : G.edgeSet) (hedge : edge.1 ∈
      (walk.map (colorPairSupportToAmbientHom C first second)).edges) :
    C edge = first ∨ C edge = second := by
  induction walk with
  | nil => simp at hedge
  | @cons u v w h walk ih =>
      rw [SimpleGraph.Walk.map_cons, SimpleGraph.Walk.edges_cons] at hedge
      have hedge' : edge.1 = s((colorPairSupportToAmbientHom C first second) u,
          (colorPairSupportToAmbientHom C first second) v) ∨
        edge.1 ∈ (walk.map (colorPairSupportToAmbientHom C first second)).edges := by
        simpa only [List.mem_cons] using hedge
      rcases hedge' with hedge | hedge
      · have hgraph : (colorPairGraph C first second).Adj u.1 v.1 := by
          simpa [colorPairSupportGraph] using h
        rcases (colorPairGraph_adj_iff C first second u.1 v.1).1 hgraph with
          ⟨hadj, hcolor⟩
        have hedgeEq : edge.1 = s(u.1, v.1) := by
          simpa [colorPairSupportToAmbientHom] using hedge
        have edgeEq : edge = ⟨s(u.1, v.1), by simpa using hadj⟩ :=
          Subtype.ext hedgeEq
        rw [edgeEq]
        simpa using hcolor
      · exact ih hedge

section RadialPathChord

/-- A remaining-color edge whose endpoints occur, in order, on one of the
two-color radial paths.  This is the source's same-path chord, before any
claim about which side of it is a disk. -/
structure MajorityChordOnRadialPath
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) where
  left : Fin (radial.path.length + 1)
  right : Fin (radial.path.length + 1)
  left_lt_right : left < right
  adjacent : G.Adj
    ((ambientRadialPath radial).getVert left)
    ((ambientRadialPath radial).getVert right)
  color : C
    ⟨s((ambientRadialPath radial).getVert left,
        (ambientRadialPath radial).getVert right), adjacent⟩ = majority

namespace MajorityChordOnRadialPath

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The unoriented ambient edge underlying a same-path chord. -/
def chordEdge
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial) :
    G.edgeSet :=
  ⟨s((ambientRadialPath radial).getVert chord.left,
      (ambientRadialPath radial).getVert chord.right), chord.adjacent⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem color_chordEdge
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial) :
    C chord.chordEdge = majority := by
  simpa [chordEdge] using chord.color

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The oriented ambient dart underlying a same-path chord. -/
def chordDart
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial) :
    G.Dart :=
  ⟨((ambientRadialPath radial).getVert chord.left,
      (ambientRadialPath radial).getVert chord.right), chord.adjacent⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The radial-path subarc between the two chord endpoints. -/
def subarc
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial) :
    G.Walk chord.chordDart.fst chord.chordDart.snd :=
  walkInterval (ambientRadialPath radial) chord.left chord.right
    (Nat.le_of_lt chord.left_lt_right)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The subarc of a radial path remains simple. -/
theorem subarc_isPath
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial) :
    chord.subarc.IsPath := by
  exact walkInterval_isPath (ambientRadialPath_isPath radial)
    chord.left chord.right (Nat.le_of_lt chord.left_lt_right)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every vertex on the chord's radial subarc remains on the complete ambient
radial path. -/
theorem subarc_support_subset_ambientRadialPath_support
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial) :
    chord.subarc.support ⊆ (ambientRadialPath radial).support := by
  have htake := SimpleGraph.Walk.isSubwalk_take
    ((ambientRadialPath radial).drop chord.left)
    (chord.right.val - chord.left.val)
  have hdrop := SimpleGraph.Walk.isSubwalk_drop
    (ambientRadialPath radial) chord.left
  have hsubwalk := htake.trans hdrop
  intro vertex hvertex
  apply hsubwalk.support_subset
  have hsupport : chord.subarc.support =
      (((ambientRadialPath radial).drop chord.left).take
        (chord.right.val - chord.left.val)).support := by
    unfold subarc walkInterval
    exact SimpleGraph.Walk.support_copy _ _ _
  rw [hsupport] at hvertex
  exact hvertex

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every vertex of the chord subarc occurs at an ambient radial-path
position between the two chord endpoints. -/
theorem exists_position_between_of_mem_subarc_support
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    {vertex : V} (hvertex : vertex ∈ chord.subarc.support) :
    ∃ position : Nat,
      chord.left.val ≤ position ∧ position ≤ chord.right.val ∧
        (ambientRadialPath radial).getVert position = vertex := by
  rcases SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvertex with
    ⟨offset, hoffsetVertex, hoffsetBound⟩
  have hrightBound : chord.right.val ≤
      (ambientRadialPath radial).length := by
    rw [ambientRadialPath_length]
    omega
  have hlength := walkInterval_length (ambientRadialPath radial)
    chord.left chord.right (Nat.le_of_lt chord.left_lt_right) hrightBound
  have hoffsetSpan : offset ≤ chord.right.val - chord.left.val := by
    change offset ≤ (walkInterval (ambientRadialPath radial)
      chord.left chord.right
        (Nat.le_of_lt chord.left_lt_right)).length at hoffsetBound
    rw [hlength] at hoffsetBound
    exact hoffsetBound
  have hpositionRight : chord.left.val + offset ≤ chord.right.val := by
    calc
      chord.left.val + offset ≤
          chord.left.val + (chord.right.val - chord.left.val) :=
        Nat.add_le_add_left hoffsetSpan chord.left.val
      _ = chord.right.val := Nat.add_sub_of_le
        (Nat.le_of_lt chord.left_lt_right)
  refine ⟨chord.left.val + offset, by omega, hpositionRight, ?_⟩
  rw [← hoffsetVertex]
  exact (walkInterval_getVert (ambientRadialPath radial)
    chord.left chord.right offset (Nat.le_of_lt chord.left_lt_right)
      hoffsetSpan).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A third-color chord cannot join consecutive positions of the selected
two-color path. -/
theorem one_lt_span
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    1 < chord.right.val - chord.left.val := by
  have hpositive : 0 < chord.right.val - chord.left.val :=
    Nat.sub_pos_of_lt chord.left_lt_right
  suffices chord.right.val - chord.left.val ≠ 1 by omega
  intro hspan
  have hright : chord.right.val = chord.left.val + 1 := by omega
  have hleft : chord.left.val < radial.path.length := by
    have hrightBound := chord.right.isLt
    omega
  have hedge : chord.chordEdge =
      ambientRadialPathStepEdge radial chord.left.val hleft := by
    apply Subtype.ext
    simp [chordEdge, ambientRadialPathStepEdge, hright]
  have hmajority :
      C (ambientRadialPathStepEdge radial chord.left.val hleft) =
        majority := by
    rw [← hedge]
    exact chord.color_chordEdge
  rcases ambientRadialPath_step_color radial chord.left.val hleft with
    hfirst | hsecond
  · exact htriple.2.2.2.1 (hmajority.symm.trans hfirst)
  · exact htriple.2.2.2.2.1 (hmajority.symm.trans hsecond)

/-- A third-color chord cannot be incident to the degree-one inner stub, so
its left endpoint is strictly inside the radial path. -/
theorem left_pos
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    0 < chord.left.val := by
  by_contra hnotPositive
  have hleft : chord.left.val = 0 := Nat.eq_zero_of_not_pos hnotPositive
  have hlength : 0 < radial.path.length := by
    have hrightBound := chord.right.isLt
    have horder := chord.left_lt_right
    omega
  have hdegree : G.degree (data.innerStub radial.inner) = 1 := by
    rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree]
    exact hdata.inner_stub_degree_one radial.inner
  rcases SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegree with
    ⟨neighbor, _hneighbor, hunique⟩
  have hchordAdj : G.Adj (data.innerStub radial.inner)
      ((ambientRadialPath radial).getVert chord.right.val) := by
    simpa [hleft, radial.start_eq_innerStub] using chord.adjacent
  have hstepAdj : G.Adj (data.innerStub radial.inner)
      ((ambientRadialPath radial).getVert 1) := by
    have hstep := (ambientRadialPath radial).adj_getVert_succ
      (i := 0) (by simpa [ambientRadialPath_length] using hlength)
    simpa [radial.start_eq_innerStub] using hstep
  have hvertices :
      (ambientRadialPath radial).getVert chord.right.val =
        (ambientRadialPath radial).getVert 1 :=
    (hunique _ hchordAdj).trans (hunique _ hstepAdj).symm
  have hright : chord.right.val = 1 :=
    (ambientRadialPath_isPath radial).getVert_injOn
      (by simpa [ambientRadialPath_length] using
        Nat.le_of_lt_succ chord.right.isLt)
      (by
        rw [ambientRadialPath_length]
        exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hlength)) hvertices
  have hspan := chord.one_lt_span htriple
  omega

/-- A third-color chord cannot be incident to the degree-one outer stub, so
its right endpoint is strictly before the end of the radial path. -/
theorem right_lt_length
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    chord.right.val < radial.path.length := by
  have hrightLe : chord.right.val ≤ radial.path.length := by
    have hrightBound := chord.right.isLt
    omega
  by_contra hnotBeforeEnd
  have hright : chord.right.val = radial.path.length := by omega
  have hlength : 0 < radial.path.length := by
    have horder := chord.left_lt_right
    omega
  have hdegree : G.degree (data.outerStub radial.outer) = 1 := by
    rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree]
    exact hdata.outer_stub_degree_one radial.outer
  rcases SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegree with
    ⟨neighbor, _hneighbor, hunique⟩
  have hchordAdj : G.Adj (data.outerStub radial.outer)
      ((ambientRadialPath radial).getVert chord.left.val) := by
    simpa [hright, ambientRadialPath_length,
      radial.finish_eq_outerStub] using chord.adjacent.symm
  have hstepAdj : G.Adj (data.outerStub radial.outer)
      ((ambientRadialPath radial).getVert (radial.path.length - 1)) := by
    have hstep := (ambientRadialPath radial).adj_getVert_succ
      (i := radial.path.length - 1) (by
        simpa [ambientRadialPath_length] using Nat.sub_lt hlength Nat.zero_lt_one)
    have hlast : radial.path.length - 1 + 1 = radial.path.length := by omega
    rw [hlast] at hstep
    have hfinish :
        (ambientRadialPath radial).getVert radial.path.length =
          data.outerStub radial.outer := by
      rw [← ambientRadialPath_length radial,
        SimpleGraph.Walk.getVert_length]
      exact radial.finish_eq_outerStub
    rw [hfinish] at hstep
    exact hstep.symm
  have hvertices :
      (ambientRadialPath radial).getVert chord.left.val =
        (ambientRadialPath radial).getVert (radial.path.length - 1) :=
    (hunique _ hchordAdj).trans (hunique _ hstepAdj).symm
  have hleft : chord.left.val = radial.path.length - 1 :=
    (ambientRadialPath_isPath radial).getVert_injOn
      (by simpa [ambientRadialPath_length] using
        Nat.le_of_lt_succ chord.left.isLt)
      (by simp [ambientRadialPath_length]) hvertices
  have hspan := chord.one_lt_span htriple
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The chord edge is not one of the subarc edges.  This is derived from the
third-color condition rather than stored as extra chord data. -/
theorem chord_not_mem_subarc
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    chord.chordDart.edge ∉ chord.subarc.edges := by
  intro hmem
  have hlengthOne := chord.subarc_isPath.length_eq_one_of_mem_edges hmem
  have hright : chord.right.val ≤ (ambientRadialPath radial).length := by
    rw [ambientRadialPath_length]
    have hrightBound := chord.right.isLt
    omega
  have hlength := walkInterval_length (ambientRadialPath radial)
    chord.left chord.right (Nat.le_of_lt chord.left_lt_right) hright
  have hspan := chord.one_lt_span htriple
  change (walkInterval (ambientRadialPath radial) chord.left chord.right
    (Nat.le_of_lt chord.left_lt_right)).length = 1 at hlengthOne
  rw [hlength] at hlengthOne
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Package an actual third-color radial-path chord as the primal wall used
by the closed-web finite face trace. -/
def boundary
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    SamePathChordBoundary G where
  chord := chord.chordDart
  subarc := chord.subarc
  subarc_isPath := chord.subarc_isPath
  chord_not_mem_subarc := chord.chord_not_mem_subarc htriple

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Traverse the chord and return along its radial-path subarc. -/
def cycleWalk
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial) :
    G.Walk chord.chordDart.fst chord.chordDart.fst :=
  chord.subarc.reverse.cons chord.chordDart.adj

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The chord and its subarc form a genuine simple cycle. -/
theorem cycleWalk_isCycle
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    chord.cycleWalk.IsCycle := by
  rw [cycleWalk, SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨chord.subarc_isPath.reverse, ?_⟩
  change chord.chordDart.edge ∉ chord.subarc.reverse.edges
  simpa using chord.chord_not_mem_subarc htriple

/-- The finite wall sent to the face trace has exactly the edges of the
simple chord cycle. -/
theorem mem_boundary_wall_iff_mem_cycleWalk_edges
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (edge : G.edgeSet) :
    edge ∈ (chord.boundary htriple).wall ↔
      edge.1 ∈ chord.cycleWalk.edges := by
  classical
  simp [boundary, SamePathChordBoundary.mem_wall_iff, cycleWalk,
    SamePathChordBoundary.chordEdge, chordDart, Subtype.ext_iff]

/-- Every endpoint of an edge in the chord cycle lies on the complete radial
path carrying the chord. -/
theorem mem_ambientRadialPath_support_of_mem_cycleWalk_edges
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (edge : G.edgeSet) (hedge : edge.1 ∈ chord.cycleWalk.edges)
    {vertex : V} (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    vertex ∈ (ambientRadialPath radial).support := by
  have hwall : edge ∈ (chord.boundary htriple).wall :=
    (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).2 hedge
  rcases ((chord.boundary htriple).mem_wall_iff edge).1 hwall with
    hedgeChord | hedgeSubarc
  · have hedgeValue : edge.1 = chord.chordDart.edge := by
      rw [hedgeChord]
      rfl
    rw [hedgeValue] at hvertex
    rcases Sym2.mem_iff.mp hvertex with hleft | hright
    · rw [hleft]
      exact (ambientRadialPath radial).getVert_mem_support chord.left
    · rw [hright]
      exact (ambientRadialPath radial).getVert_mem_support chord.right
  · exact chord.subarc_support_subset_ambientRadialPath_support
      (chord.subarc.mem_support_of_mem_edges hedgeSubarc hvertex)

/-- The remaining-color edge at a strict interior radial-path position is an
external port of the chord wall.  Thus the cycle contains only the two
selected-color path edges at such a position; its third edge leaves the wall.
This is the local port fact needed before a global side predicate can be
constructed. -/
theorem thirdColor_edge_not_mem_cycleWalk_of_interior
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (position : Nat) (hposition : position ≤ radial.path.length)
    (hinterior : chord.left.val < position ∧ position < chord.right.val)
    (edge : G.edgeSet)
    (hincident : (ambientRadialPath radial).getVert position ∈
      (edge.1 : Sym2 V))
    (hcolor : C edge = first + second) :
    edge.1 ∉ chord.cycleWalk.edges := by
  intro hedge
  have hwall : edge ∈ (chord.boundary htriple).wall :=
    (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).2 hedge
  rcases ((chord.boundary htriple).mem_wall_iff edge).1 hwall with
    hedgeChord | hedgeSubarc
  · have hedgeValue : edge.1 = chord.chordDart.edge := by
      rw [hedgeChord]
      rfl
    rw [hedgeValue] at hincident
    rcases Sym2.mem_iff.mp hincident with hleft | hright
    · have hposEq : position = chord.left.val :=
        (ambientRadialPath_isPath radial).getVert_injOn
          (by simpa [ambientRadialPath_length] using hposition)
          (by simpa [ambientRadialPath_length] using
            Nat.le_of_lt_succ chord.left.isLt) hleft
      omega
    · have hposEq : position = chord.right.val :=
        (ambientRadialPath_isPath radial).getVert_injOn
          (by simpa [ambientRadialPath_length] using hposition)
          (by simpa [ambientRadialPath_length] using
            Nat.le_of_lt_succ chord.right.isLt) hright
      omega
  · have htake := SimpleGraph.Walk.isSubwalk_take
      ((ambientRadialPath radial).drop chord.left)
      (chord.right.val - chord.left.val)
    have hdrop := SimpleGraph.Walk.isSubwalk_drop
      (ambientRadialPath radial) chord.left
    have hsubwalk := htake.trans hdrop
    have hambient : edge.1 ∈ (ambientRadialPath radial).edges := by
      apply hsubwalk.edges_subset
      have hedgeSubarc' : edge.1 ∈ chord.subarc.edges := by
        simpa only [MajorityChordOnRadialPath.boundary] using hedgeSubarc
      change edge.1 ∈ (walkInterval (ambientRadialPath radial)
        chord.left chord.right (Nat.le_of_lt chord.left_lt_right)).edges at hedgeSubarc'
      unfold walkInterval at hedgeSubarc'
      rw [SimpleGraph.Walk.edges_copy] at hedgeSubarc'
      exact hedgeSubarc'
    have hmapped := hambient
    change edge.1 ∈
      (radial.path.map (colorPairSupportToAmbientHom C first second)).edges at hmapped
    rcases mapped_walk_edges_color_pair (walk := radial.path)
      (edge := edge) hmapped with hfirst | hsecond
    · have hthird := third_color_properties htriple.2.1
          htriple.2.2.1 htriple.2.2.2.2.2
      exact hthird.2.1 (hcolor.symm.trans hfirst)
    · have hthird := third_color_properties htriple.2.1
          htriple.2.2.1 htriple.2.2.2.2.2
      exact hthird.2.2 (hcolor.symm.trans hsecond)

/-- At every strict interior radial-path position, cubicity supplies a
remaining-color edge, and the preceding theorem proves that edge is an
external port of the chord wall. -/
theorem exists_thirdColor_external_port_of_interior
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (position : Nat) (hposition : position ≤ radial.path.length)
    (hinterior : chord.left.val < position ∧ position < chord.right.val) :
    ∃ edge : G.edgeSet,
      (ambientRadialPath radial).getVert position ∈
        (edge.1 : Sym2 V) ∧
      C edge = first + second ∧
      edge.1 ∉ chord.cycleWalk.edges := by
  have hcubic := ambientRadialPath_internal_incidentEdgeFinset_card_eq_three
    hdata radial position (by omega) (by omega)
  have hthird := third_color_properties htriple.2.1
    htriple.2.2.1 htriple.2.2.2.2.2
  rcases GoertzelV24FramedTrail.exists_incident_edge_of_color_of_cubic_tait
      C hC ((ambientRadialPath radial).getVert position) hcubic
      (first + second) hthird.1 with
    ⟨edge, hedge, hcolor⟩
  have hincident : (ambientRadialPath radial).getVert position ∈
      (edge.1 : Sym2 V) := by
    simpa [incidentEdgeFinset] using hedge
  refine ⟨edge, hincident, hcolor, ?_⟩
  exact thirdColor_edge_not_mem_cycleWalk_of_interior chord htriple
    position hposition hinterior edge hincident hcolor

/- The chord endpoints also expose the selected-color path step as one of
the two wall edges.  Cubicity therefore supplies the other selected color as
an external port; this is the endpoint half of the local separator audit. -/
theorem exists_left_external_port
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    ∃ edge : G.edgeSet,
      (ambientRadialPath radial).getVert chord.left.val ∈
        (edge.1 : Sym2 V) ∧
      edge.1 ∉ chord.cycleWalk.edges := by
  have hleftLength : chord.left.val < radial.path.length := by
    have hrightLength := chord.right_lt_length hdata htriple
    have hleftRight : chord.left.val < chord.right.val := chord.left_lt_right
    omega
  have hleftPos := chord.left_pos hdata htriple
  have hstep := ambientRadialPath_step_color radial chord.left.val hleftLength
  rcases hstep with hfirst | hsecond
  · have htarget : second ≠ 0 := htriple.2.2.1
    rcases GoertzelV24FramedTrail.exists_incident_edge_of_color_of_cubic_tait
        C hC ((ambientRadialPath radial).getVert chord.left.val)
        (by
          exact ambientRadialPath_internal_incidentEdgeFinset_card_eq_three
            hdata radial chord.left.val (by omega) hleftLength)
        second htarget with
      ⟨edge, hedge, hedgeColor⟩
    have hincident : (ambientRadialPath radial).getVert chord.left.val ∈
        (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hedge
    refine ⟨edge, hincident, ?_⟩
    intro hcycle
    have hwall : edge ∈ (chord.boundary htriple).wall :=
      (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).2 hcycle
    rcases ((chord.boundary htriple).mem_wall_iff edge).1 hwall with
      hchord | hsubarc
    · have hedgeValue : edge.1 = chord.chordDart.edge := by
        rw [hchord]
        rfl
      have hmajority : C edge = majority := by
        have hedgeSubtype : edge = chord.chordEdge := by
          apply Subtype.ext
          exact hedgeValue
        rw [hedgeSubtype]
        exact chord.color_chordEdge
      exact htriple.2.2.2.2.1 (hmajority.symm.trans hedgeColor)
    · have hsubarc' : edge.1 ∈ chord.subarc.edges := by
        simpa only [MajorityChordOnRadialPath.boundary] using hsubarc
      rcases Sym2.mem_iff_exists.mp hincident with ⟨neighbor, hedgePair⟩
      have hsubarcMem : s((ambientRadialPath radial).getVert chord.left.val,
          neighbor) ∈ chord.subarc.edges := by
        rw [← hedgePair]
        exact hsubarc'
      have hneighbor : neighbor = chord.subarc.snd := by
        apply chord.subarc_isPath.eq_snd_of_mem_edges
        simpa [MajorityChordOnRadialPath.subarc,
          MajorityChordOnRadialPath.chordDart] using hsubarcMem
      have hstepEdge :
          (⟨s((ambientRadialPath radial).getVert chord.left.val,
            (ambientRadialPath radial).getVert (chord.left.val + 1)), by
              simpa using (ambientRadialPath radial).adj_getVert_succ
                (i := chord.left.val)
                (by simpa [ambientRadialPath_length] using hleftLength)⟩ : G.edgeSet) = edge := by
        apply Subtype.ext
        have hsubarcSnd : chord.subarc.snd =
            (ambientRadialPath radial).getVert (chord.left.val + 1) := by
          have hraw :
              (walkInterval (ambientRadialPath radial) chord.left.val chord.right.val
                (Nat.le_of_lt chord.left_lt_right)).snd =
                (ambientRadialPath radial).getVert (chord.left.val + 1) := by
            change (walkInterval (ambientRadialPath radial) chord.left.val
              chord.right.val (Nat.le_of_lt chord.left_lt_right)).getVert 1 = _
            simpa [walkInterval] using
              (walkInterval_getVert (ambientRadialPath radial) chord.left.val
                chord.right.val 1 (Nat.le_of_lt chord.left_lt_right) (by
                  have hspan := chord.one_lt_span htriple
                  omega))
          change (walkInterval (ambientRadialPath radial) chord.left.val chord.right.val
            (Nat.le_of_lt chord.left_lt_right)).snd = _
          exact hraw
        calc
          s((ambientRadialPath radial).getVert chord.left.val,
              (ambientRadialPath radial).getVert (chord.left.val + 1)) =
              s(chord.chordDart.fst, chord.subarc.snd) := by
                rw [hsubarcSnd]
                rfl
          _ = s((ambientRadialPath radial).getVert chord.left.val, neighbor) := by
                rw [hneighbor]
                rfl
          _ = edge.1 := hedgePair.symm
      have : C edge = first := by
        rw [← hstepEdge]
        simpa [ambientRadialPathStepEdge] using hfirst
      exact htriple.2.2.2.2.2 (this.symm.trans hedgeColor)
  · have htarget : first ≠ 0 := htriple.2.1
    rcases GoertzelV24FramedTrail.exists_incident_edge_of_color_of_cubic_tait
        C hC ((ambientRadialPath radial).getVert chord.left.val)
        (by
          exact ambientRadialPath_internal_incidentEdgeFinset_card_eq_three
            hdata radial chord.left.val (by omega) hleftLength)
        first htarget with
      ⟨edge, hedge, hedgeColor⟩
    have hincident : (ambientRadialPath radial).getVert chord.left.val ∈
        (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hedge
    refine ⟨edge, hincident, ?_⟩
    intro hcycle
    have hwall : edge ∈ (chord.boundary htriple).wall :=
      (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).2 hcycle
    rcases ((chord.boundary htriple).mem_wall_iff edge).1 hwall with
      hchord | hsubarc
    · have hedgeValue : edge.1 = chord.chordDart.edge := by
        rw [hchord]
        rfl
      have hmajority : C edge = majority := by
        have hedgeSubtype : edge = chord.chordEdge := by
          apply Subtype.ext
          exact hedgeValue
        rw [hedgeSubtype]
        exact chord.color_chordEdge
      exact htriple.2.2.2.1 (hmajority.symm.trans hedgeColor)
    · have hsubarc' : edge.1 ∈ chord.subarc.edges := by
        simpa only [MajorityChordOnRadialPath.boundary] using hsubarc
      rcases Sym2.mem_iff_exists.mp hincident with ⟨neighbor, hedgePair⟩
      have hsubarcMem : s((ambientRadialPath radial).getVert chord.left.val,
          neighbor) ∈ chord.subarc.edges := by
        rw [← hedgePair]
        exact hsubarc'
      have hneighbor : neighbor = chord.subarc.snd := by
        apply chord.subarc_isPath.eq_snd_of_mem_edges
        simpa [MajorityChordOnRadialPath.subarc,
          MajorityChordOnRadialPath.chordDart] using hsubarcMem
      have hstepEdge :
          (⟨s((ambientRadialPath radial).getVert chord.left.val,
            (ambientRadialPath radial).getVert (chord.left.val + 1)), by
              simpa using (ambientRadialPath radial).adj_getVert_succ
                (i := chord.left.val)
                (by simpa [ambientRadialPath_length] using hleftLength)⟩ : G.edgeSet) = edge := by
        apply Subtype.ext
        have hsubarcSnd : chord.subarc.snd =
            (ambientRadialPath radial).getVert (chord.left.val + 1) := by
          have hraw :
              (walkInterval (ambientRadialPath radial) chord.left.val chord.right.val
                (Nat.le_of_lt chord.left_lt_right)).snd =
                (ambientRadialPath radial).getVert (chord.left.val + 1) := by
            change (walkInterval (ambientRadialPath radial) chord.left.val
              chord.right.val (Nat.le_of_lt chord.left_lt_right)).getVert 1 = _
            simpa [walkInterval] using
              (walkInterval_getVert (ambientRadialPath radial) chord.left.val
                chord.right.val 1 (Nat.le_of_lt chord.left_lt_right) (by
                  have hspan := chord.one_lt_span htriple
                  omega))
          change (walkInterval (ambientRadialPath radial) chord.left.val chord.right.val
            (Nat.le_of_lt chord.left_lt_right)).snd = _
          exact hraw
        calc
          s((ambientRadialPath radial).getVert chord.left.val,
              (ambientRadialPath radial).getVert (chord.left.val + 1)) =
              s(chord.chordDart.fst, chord.subarc.snd) := by
                rw [hsubarcSnd]
                rfl
          _ = s((ambientRadialPath radial).getVert chord.left.val, neighbor) := by
                rw [hneighbor]
                rfl
          _ = edge.1 := hedgePair.symm
      have : C edge = second := by
        rw [← hstepEdge]
        simpa [ambientRadialPathStepEdge] using hsecond
      exact htriple.2.2.2.2.2 (hedgeColor.symm.trans this)

/- The same cubic audit at the right endpoint.  The radial step is read
backwards here, so the path's penultimate-vertex lemma identifies the only
possible selected-color wall edge at that endpoint. -/
theorem exists_right_external_port
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second) :
    ∃ edge : G.edgeSet,
      (ambientRadialPath radial).getVert chord.right.val ∈
        (edge.1 : Sym2 V) ∧
      edge.1 ∉ chord.cycleWalk.edges := by
  have hrightLength := chord.right_lt_length hdata htriple
  have hrightPos : 0 < chord.right.val := by
    have hleftPos := chord.left_pos hdata htriple
    exact Nat.lt_trans hleftPos chord.left_lt_right
  have hrightOne : 1 ≤ chord.right.val := by omega
  have hprevAdd : chord.right.val - 1 + 1 = chord.right.val :=
    Nat.sub_add_cancel hrightOne
  have hprevious : chord.right.val - 1 < radial.path.length := by
    omega
  have hstep := ambientRadialPath_step_color radial
    (chord.right.val - 1) hprevious
  have hsubarcPenultimate : chord.subarc.penultimate =
      (ambientRadialPath radial).getVert (chord.right.val - 1) := by
    change (walkInterval (ambientRadialPath radial) chord.left.val chord.right.val
      (Nat.le_of_lt chord.left_lt_right)).getVert
        ((walkInterval (ambientRadialPath radial) chord.left.val chord.right.val
          (Nat.le_of_lt chord.left_lt_right)).length - 1) = _
    rw [walkInterval_length (ambientRadialPath radial) chord.left.val chord.right.val
      (Nat.le_of_lt chord.left_lt_right)
      (by simpa [ambientRadialPath_length] using Nat.le_of_lt hrightLength)]
    rw [walkInterval_getVert (ambientRadialPath radial) chord.left.val chord.right.val
      (chord.right.val - chord.left.val - 1)
      (Nat.le_of_lt chord.left_lt_right) (Nat.sub_le _ _)]
    congr 1
    have hspan := chord.one_lt_span htriple
    omega
  rcases hstep with hfirst | hsecond
  · have htarget : second ≠ 0 := htriple.2.2.1
    rcases GoertzelV24FramedTrail.exists_incident_edge_of_color_of_cubic_tait
        C hC ((ambientRadialPath radial).getVert chord.right.val)
        (by
          exact ambientRadialPath_internal_incidentEdgeFinset_card_eq_three
            hdata radial chord.right.val (by omega) hrightLength)
        second htarget with
      ⟨edge, hedge, hedgeColor⟩
    have hincident : (ambientRadialPath radial).getVert chord.right.val ∈
        (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hedge
    refine ⟨edge, hincident, ?_⟩
    intro hcycle
    have hwall : edge ∈ (chord.boundary htriple).wall :=
      (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).2 hcycle
    rcases ((chord.boundary htriple).mem_wall_iff edge).1 hwall with
      hchord | hsubarc
    · have hedgeValue : edge.1 = chord.chordDart.edge := by
        rw [hchord]
        rfl
      have hmajority : C edge = majority := by
        have hedgeSubtype : edge = chord.chordEdge := by
          apply Subtype.ext
          exact hedgeValue
        rw [hedgeSubtype]
        exact chord.color_chordEdge
      exact htriple.2.2.2.2.1 (hmajority.symm.trans hedgeColor)
    · have hsubarc' : edge.1 ∈ chord.subarc.edges := by
        simpa only [MajorityChordOnRadialPath.boundary] using hsubarc
      rcases Sym2.mem_iff_exists.mp hincident with ⟨neighbor, hedgePair⟩
      have hsubarcMem : s((ambientRadialPath radial).getVert chord.right.val,
          neighbor) ∈ chord.subarc.edges := by
        rw [← hedgePair]
        exact hsubarc'
      have hneighbor : neighbor = chord.subarc.penultimate := by
        apply chord.subarc_isPath.eq_penultimate_of_mem_edges
        exact hsubarcMem
      have hstepEdge :
          (⟨s((ambientRadialPath radial).getVert (chord.right.val - 1),
            (ambientRadialPath radial).getVert chord.right.val), by
              have hstepAdj := (ambientRadialPath radial).adj_getVert_succ
                (i := chord.right.val - 1) (by
                  simpa [ambientRadialPath_length] using hprevious)
              have hprevAdd : chord.right.val - 1 + 1 = chord.right.val :=
                Nat.sub_add_cancel hrightOne
              rw [hprevAdd] at hstepAdj
              exact hstepAdj⟩ :
            G.edgeSet) = edge := by
        apply Subtype.ext
        calc
          s((ambientRadialPath radial).getVert (chord.right.val - 1),
              (ambientRadialPath radial).getVert chord.right.val) =
              s(chord.subarc.penultimate,
                (ambientRadialPath radial).getVert chord.right.val) := by
                  rw [hsubarcPenultimate]
          _ = s((ambientRadialPath radial).getVert chord.right.val, neighbor) := by
                rw [hneighbor]
                exact Sym2.eq_swap
          _ = edge.1 := hedgePair.symm
      have : C edge = first := by
        have hstepEdge' : ambientRadialPathStepEdge radial
            (chord.right.val - 1) hprevious = edge := by
          apply Subtype.ext
          change s((ambientRadialPath radial).getVert (chord.right.val - 1),
            (ambientRadialPath radial).getVert (chord.right.val - 1 + 1)) = edge.1
          rw [hprevAdd]
          exact congrArg Subtype.val hstepEdge
        rw [← hstepEdge']
        exact hfirst
      exact htriple.2.2.2.2.2 (this.symm.trans hedgeColor)
  · have htarget : first ≠ 0 := htriple.2.1
    rcases GoertzelV24FramedTrail.exists_incident_edge_of_color_of_cubic_tait
        C hC ((ambientRadialPath radial).getVert chord.right.val)
        (by
          exact ambientRadialPath_internal_incidentEdgeFinset_card_eq_three
            hdata radial chord.right.val (by omega) hrightLength)
        first htarget with
      ⟨edge, hedge, hedgeColor⟩
    have hincident : (ambientRadialPath radial).getVert chord.right.val ∈
        (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hedge
    refine ⟨edge, hincident, ?_⟩
    intro hcycle
    have hwall : edge ∈ (chord.boundary htriple).wall :=
      (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).2 hcycle
    rcases ((chord.boundary htriple).mem_wall_iff edge).1 hwall with
      hchord | hsubarc
    · have hedgeValue : edge.1 = chord.chordDart.edge := by
        rw [hchord]
        rfl
      have hmajority : C edge = majority := by
        have hedgeSubtype : edge = chord.chordEdge := by
          apply Subtype.ext
          exact hedgeValue
        rw [hedgeSubtype]
        exact chord.color_chordEdge
      exact htriple.2.2.2.1 (hmajority.symm.trans hedgeColor)
    · have hsubarc' : edge.1 ∈ chord.subarc.edges := by
        simpa only [MajorityChordOnRadialPath.boundary] using hsubarc
      rcases Sym2.mem_iff_exists.mp hincident with ⟨neighbor, hedgePair⟩
      have hsubarcMem : s((ambientRadialPath radial).getVert chord.right.val,
          neighbor) ∈ chord.subarc.edges := by
        rw [← hedgePair]
        exact hsubarc'
      have hneighbor : neighbor = chord.subarc.penultimate := by
        apply chord.subarc_isPath.eq_penultimate_of_mem_edges
        exact hsubarcMem
      have hstepEdge :
          (⟨s((ambientRadialPath radial).getVert (chord.right.val - 1),
            (ambientRadialPath radial).getVert chord.right.val), by
              have hstepAdj := (ambientRadialPath radial).adj_getVert_succ
                (i := chord.right.val - 1) (by
                  simpa [ambientRadialPath_length] using hprevious)
              have hprevAdd : chord.right.val - 1 + 1 = chord.right.val :=
                Nat.sub_add_cancel hrightOne
              rw [hprevAdd] at hstepAdj
              exact hstepAdj⟩ :
            G.edgeSet) = edge := by
        apply Subtype.ext
        calc
          s((ambientRadialPath radial).getVert (chord.right.val - 1),
              (ambientRadialPath radial).getVert chord.right.val) =
              s(chord.subarc.penultimate,
                (ambientRadialPath radial).getVert chord.right.val) := by
                  rw [hsubarcPenultimate]
          _ = s((ambientRadialPath radial).getVert chord.right.val, neighbor) := by
                rw [hneighbor]
                exact Sym2.eq_swap
          _ = edge.1 := hedgePair.symm
      have : C edge = second := by
        have hstepEdge' : ambientRadialPathStepEdge radial
            (chord.right.val - 1) hprevious = edge := by
          apply Subtype.ext
          change s((ambientRadialPath radial).getVert (chord.right.val - 1),
            (ambientRadialPath radial).getVert (chord.right.val - 1 + 1)) = edge.1
          rw [hprevAdd]
          exact congrArg Subtype.val hstepEdge
        rw [← hstepEdge']
        exact hsecond
      exact htriple.2.2.2.2.2 (hedgeColor.symm.trans this)

/- The three local port lemmas compose into one interval-level certificate.
This is the exact reusable input for a later separator construction: it says
where the wall can leave the radial carrier, but deliberately does not choose
the global side or claim a bound on the number of such ports. -/
theorem exists_external_port_on_chord_interval
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (position : Nat) (hleft : chord.left.val ≤ position)
    (hright : position ≤ chord.right.val) :
    ∃ edge : G.edgeSet,
      (ambientRadialPath radial).getVert position ∈
        (edge.1 : Sym2 V) ∧
      edge.1 ∉ chord.cycleWalk.edges := by
  by_cases hleftEq : position = chord.left.val
  · subst position
    exact chord.exists_left_external_port hdata hC htriple
  by_cases hrightEq : position = chord.right.val
  · subst position
    exact chord.exists_right_external_port hdata hC htriple
  have hinterior : chord.left.val < position ∧ position < chord.right.val := by
    omega
  rcases chord.exists_thirdColor_external_port_of_interior hdata hC htriple
      position (by
        have hrightLength := chord.right_lt_length hdata htriple
        omega) hinterior with
    ⟨edge, hincident, _hcolor, hnotWall⟩
  exact ⟨edge, hincident, hnotWall⟩

/-!
The interval theorem is existential, which is the right statement for the
local cubic argument but awkward for the next (side-construction) layer.  The
following choice packages exactly that information into a function on the
finite interval.  It is intentionally only a choice of an *external
incident edge*: it does not choose a face component or claim that the chosen
ports form the global crossing set of the chord wall.
-/

noncomputable def externalPortOnChordInterval
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (position : {position : Nat //
      chord.left.val ≤ position ∧ position ≤ chord.right.val}) : G.edgeSet :=
  Classical.choose
    (chord.exists_external_port_on_chord_interval hdata hC htriple
      position.1 position.2.1 position.2.2)

theorem externalPortOnChordInterval_incident
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (position : {position : Nat //
      chord.left.val ≤ position ∧ position ≤ chord.right.val}) :
    (ambientRadialPath radial).getVert position.1 ∈
      ((externalPortOnChordInterval hdata hC chord htriple position).1 : Sym2 V) := by
  exact (Classical.choose_spec
    (chord.exists_external_port_on_chord_interval hdata hC htriple
      position.1 position.2.1 position.2.2)).1

theorem externalPortOnChordInterval_not_cycleWalk
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (position : {position : Nat //
      chord.left.val ≤ position ∧ position ≤ chord.right.val}) :
    (externalPortOnChordInterval hdata hC chord htriple position).1 ∉
      chord.cycleWalk.edges := by
  exact (Classical.choose_spec
    (chord.exists_external_port_on_chord_interval hdata hC htriple
      position.1 position.2.1 position.2.2)).2

/-- Every endpoint of a chord-cycle edge occurs between the chord endpoints
on the complete radial path. -/
theorem exists_position_between_of_mem_cycleWalk_edges
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (edge : G.edgeSet) (hedge : edge.1 ∈ chord.cycleWalk.edges)
    {vertex : V} (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    ∃ position : Nat,
      chord.left.val ≤ position ∧ position ≤ chord.right.val ∧
        (ambientRadialPath radial).getVert position = vertex := by
  have hwall : edge ∈ (chord.boundary htriple).wall :=
    (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).2 hedge
  rcases ((chord.boundary htriple).mem_wall_iff edge).1 hwall with
    hedgeChord | hedgeSubarc
  · have hedgeValue : edge.1 = chord.chordDart.edge := by
      rw [hedgeChord]
      rfl
    rw [hedgeValue] at hvertex
    rcases Sym2.mem_iff.mp hvertex with hleft | hright
    · exact ⟨chord.left.val, le_rfl,
        Nat.le_of_lt chord.left_lt_right, hleft.symm⟩
    · exact ⟨chord.right.val, Nat.le_of_lt chord.left_lt_right,
        le_rfl, hright.symm⟩
  · exact chord.exists_position_between_of_mem_subarc_support
      (chord.subarc.mem_support_of_mem_edges hedgeSubarc hvertex)

/-!
Every wall-edge endpoint inherits the same local certificate.  This is the
useful bridge from the interval-coordinate proof to the wall support: it says
that a cycle vertex has at least one incident ambient edge which is not on the
cycle.  The theorem still makes no global side assignment; it only supplies
the off-wall incidence needed by a later primal Jordan construction.
-/

theorem exists_external_port_at_cycleWalk_vertex
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (edge : G.edgeSet) (hedge : edge.1 ∈ chord.cycleWalk.edges)
    {vertex : V} (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    ∃ port : G.edgeSet,
      vertex ∈ (port.1 : Sym2 V) ∧ port.1 ∉ chord.cycleWalk.edges := by
  rcases chord.exists_position_between_of_mem_cycleWalk_edges htriple
      edge hedge hvertex with
    ⟨position, hleft, hright, hposition⟩
  rcases chord.exists_external_port_on_chord_interval hdata hC htriple
      position hleft hright with
    ⟨port, hportVertex, hportOutside⟩
  exact ⟨port, by simpa [hposition] using hportVertex, hportOutside⟩

/-!
The face-tracing layer works with rotation-system darts, while the chord
certificate above is stated with ordinary graph edges.  For an off-wall
vertex these representations line up directly: every incident rotation dart
has an edge outside the cycle.  This is the exact hypothesis consumed by
`faceComponentSide_iff_of_anchor_of_vertex_avoids`.
-/

theorem toRotationSystem_edge_not_mem_cycleWalk_of_vertex_not_mem_support
    (graphData : SimpleGraphDartRotation.Data G)
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    {vertex : V} (hvertex : vertex ∉ chord.cycleWalk.support)
    (dart : graphData.toRotationSystem.D)
    (hdart : graphData.toRotationSystem.vertOf dart = vertex) :
    (graphData.toRotationSystem.edgeOf dart).1 ∉ chord.cycleWalk.edges := by
  intro hcycle
  have hvertexEdge : graphData.toRotationSystem.vertOf dart ∈
      ((graphData.toRotationSystem.edgeOf dart).1 : Sym2 V) := by
    change dart.fst ∈ dart.edge
    simp [SimpleGraph.Dart.edge]
  have hsupport : graphData.toRotationSystem.vertOf dart ∈
      chord.cycleWalk.support := by
    exact chord.cycleWalk.mem_support_of_mem_edges hcycle hvertexEdge
  exact hvertex (hdart ▸ hsupport)

theorem toRotationSystem_all_incident_edges_not_mem_cycleWalk_of_vertex_not_mem_support
    (graphData : SimpleGraphDartRotation.Data G)
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    {vertex : V} (hvertex : vertex ∉ chord.cycleWalk.support) :
    ∀ dart : graphData.toRotationSystem.D,
      graphData.toRotationSystem.vertOf dart = vertex →
        (graphData.toRotationSystem.edgeOf dart).1 ∉ chord.cycleWalk.edges := by
  intro dart hdart
  exact chord.toRotationSystem_edge_not_mem_cycleWalk_of_vertex_not_mem_support
    graphData hvertex dart hdart

/-- Every endpoint of every chord-cycle edge is a locally cubic annular
interior vertex. -/
theorem cycleWalk_edge_endpoint_incidentEdgeFinset_card_eq_three
    {data : AnnularBoundaryData G outerCount} (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (edge : G.edgeSet) (hedge : edge.1 ∈ chord.cycleWalk.edges)
    {vertex : V} (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    (incidentEdgeFinset G vertex).card = 3 := by
  rcases chord.exists_position_between_of_mem_cycleWalk_edges htriple
      edge hedge hvertex with
    ⟨position, hleft, hright, hposition⟩
  have hpositive : position ≠ 0 := by
    have := chord.left_pos hdata htriple
    omega
  have hbeforeEnd : position < radial.path.length := by
    have := chord.right_lt_length hdata htriple
    omega
  have hcubic := ambientRadialPath_internal_incidentEdgeFinset_card_eq_three
    hdata radial position hpositive hbeforeEnd
  rwa [hposition] at hcubic

end MajorityChordOnRadialPath

end RadialPathChord

end GoertzelV24ClosedWebRadialPathChords

end Mettapedia.GraphTheory.FourColor
