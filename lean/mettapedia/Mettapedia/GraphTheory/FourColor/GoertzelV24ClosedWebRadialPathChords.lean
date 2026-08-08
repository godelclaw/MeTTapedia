import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialComponents
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFaceTracing

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

section WalkInterval

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The oriented interval of a walk between two ordered vertex positions. -/
def walkInterval {start finish : V} (walk : G.Walk start finish)
    (left right : Nat) (horder : left ≤ right) :
    G.Walk (walk.getVert left) (walk.getVert right) :=
  ((walk.drop left).take (right - left)).copy rfl (by
    simp [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le horder])

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Taking an interval of a path again gives a path. -/
theorem walkInterval_isPath {start finish : V}
    {walk : G.Walk start finish} (hwalk : walk.IsPath)
    (left right : Nat) (horder : left ≤ right) :
    (walkInterval walk left right horder).IsPath := by
  simpa [walkInterval] using (hwalk.drop left).take (right - left)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Within the range of the original walk, an interval has the expected
number of edges. -/
theorem walkInterval_length {start finish : V}
    (walk : G.Walk start finish) (left right : Nat)
    (horder : left ≤ right) (hright : right ≤ walk.length) :
    (walkInterval walk left right horder).length = right - left := by
  simp only [walkInterval, SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length]
  rw [Nat.min_eq_left]
  omega

end WalkInterval

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

end MajorityChordOnRadialPath

end RadialPathChord

end GoertzelV24ClosedWebRadialPathChords

end Mettapedia.GraphTheory.FourColor
