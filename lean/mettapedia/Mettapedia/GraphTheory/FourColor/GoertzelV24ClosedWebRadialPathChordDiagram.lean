import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChords

/-!
# The finite third-color chord diagram on a v24 radial path

This module turns the individual same-path chords into the finite ordered
diagram used by the Sector-Alternation argument.  Its main theorem is purely
graph-theoretic: properness of the Tait edge coloring makes the third color a
matching, so distinct chords cannot share an endpoint position on the simple
radial path.

Planar noncrossing and hole-free-side claims are intentionally absent.  They
belong to the rotation/cellulation bridge, not to edge-coloring properness.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebRadialPathChordDiagram

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebSelectedEdgeStructure

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- An ordered pair of radial-path positions is joined by an ambient edge of
the third color. -/
def IsMajorityChordAt
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component)
    (position : OrderedPathChord (radial.path.length + 1)) : Prop :=
  ∃ hadjacent : G.Adj
      ((ambientRadialPath radial).getVert position.left)
      ((ambientRadialPath radial).getVert position.right),
    C ⟨s((ambientRadialPath radial).getVert position.left,
        (ambientRadialPath radial).getVert position.right), hadjacent⟩ = majority

/-- The finite ordered diagram of all third-color same-path chords. -/
def majorityChordDiagram
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    Finset (OrderedPathChord (radial.path.length + 1)) := by
  classical
  exact Finset.univ.filter fun position =>
    IsMajorityChordAt C majority first second radial position

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_majorityChordDiagram_iff
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    {position : OrderedPathChord (radial.path.length + 1)} :
    position ∈ majorityChordDiagram C majority first second radial ↔
      IsMajorityChordAt C majority first second radial position := by
  classical
  simp [majorityChordDiagram]

/-- Materialize a diagram member as the individual chord object used by the
face-tracing bridge. -/
def majorityChordOfPosition
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (position : OrderedPathChord (radial.path.length + 1))
    (hposition : IsMajorityChordAt
      C majority first second radial position) :
    MajorityChordOnRadialPath C majority first second radial :=
  { left := position.left
    right := position.right
    left_lt_right := position.left_lt_right
    adjacent := Classical.choose hposition
    color := Classical.choose_spec hposition }

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two third-color edges leaving the same radial-path position must have the
same other endpoint position. -/
theorem otherEndpoint_eq_of_majority_adj
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    {root left right : Fin (radial.path.length + 1)}
    (hleft : (colorClassGraph C majority).Adj
      ((ambientRadialPath radial).getVert root)
      ((ambientRadialPath radial).getVert left))
    (hright : (colorClassGraph C majority).Adj
      ((ambientRadialPath radial).getVert root)
      ((ambientRadialPath radial).getVert right)) :
    left = right := by
  rcases colorClassGraph_existsUnique_adj C majority hleft.mem_support_left with
    ⟨neighbor, _hneighbor, hunique⟩
  apply ambientRadialPath_getVert_injective radial
  exact (hunique _ hleft).trans (hunique _ hright).symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The actual third-color chord diagram is a matching on ordered path
positions.  This discharges the endpoint-disjoint premise in the corrected
innermost-chord lemma without using planarity. -/
theorem majorityChordDiagram_pairwiseEndpointDisjoint
    {data : AnnularBoundaryData G outerCount}
    (C : G.EdgeColoring Color) (majority first second : Color)
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    (radial : ComponentRadialPath data C first second component) :
    PairwiseEndpointDisjoint
      (majorityChordDiagram C majority first second radial) := by
  intro firstChord hfirst secondChord hsecond hne
  rw [mem_majorityChordDiagram_iff] at hfirst hsecond
  rcases hfirst with ⟨hfirstAdj, hfirstColor⟩
  rcases hsecond with ⟨hsecondAdj, hsecondColor⟩
  have hfirstClass : (colorClassGraph C majority).Adj
      ((ambientRadialPath radial).getVert firstChord.left)
      ((ambientRadialPath radial).getVert firstChord.right) :=
    (colorClassGraph_adj_iff C majority _ _).2
      ⟨hfirstAdj, hfirstColor⟩
  have hsecondClass : (colorClassGraph C majority).Adj
      ((ambientRadialPath radial).getVert secondChord.left)
      ((ambientRadialPath radial).getVert secondChord.right) :=
    (colorClassGraph_adj_iff C majority _ _).2
      ⟨hsecondAdj, hsecondColor⟩
  constructor
  · intro hleftLeft
    have hrightRight : firstChord.right = secondChord.right :=
      otherEndpoint_eq_of_majority_adj hfirstClass (hleftLeft ▸ hsecondClass)
    apply hne
    cases firstChord
    cases secondChord
    simp_all
  constructor
  · intro hleftRight
    have hrightLeft : firstChord.right = secondChord.left :=
      otherEndpoint_eq_of_majority_adj hfirstClass
        (hleftRight ▸ hsecondClass.symm)
    have hfirstOrder := firstChord.left_lt_right
    have hsecondOrder := secondChord.left_lt_right
    omega
  constructor
  · intro hrightLeft
    have hleftRight : firstChord.left = secondChord.right :=
      otherEndpoint_eq_of_majority_adj hfirstClass.symm
        (hrightLeft ▸ hsecondClass)
    have hfirstOrder := firstChord.left_lt_right
    have hsecondOrder := secondChord.left_lt_right
    omega
  · intro hrightRight
    have hleftLeft : firstChord.left = secondChord.left :=
      otherEndpoint_eq_of_majority_adj hfirstClass.symm
        (hrightRight ▸ hsecondClass.symm)
    apply hne
    cases firstChord
    cases secondChord
    simp_all

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every nonempty finite radial-path chord diagram has an innermost member.
Choose a chord of minimum endpoint span; a strictly nested chord would have
strictly smaller span.  This is the finite selection step used before the
source's sector-drainage argument. -/
theorem exists_innermost_majorityChord
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (hnonempty :
      (majorityChordDiagram C majority first second radial).Nonempty) :
    ∃ chord ∈ majorityChordDiagram C majority first second radial,
      InnermostIn chord
        (majorityChordDiagram C majority first second radial) := by
  exact exists_innermost_orderedPathChord hnonempty

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every distinct actual chord touching the open subarc of an innermost
chord must strictly interleave it.  A chord wholly inside would contradict
innermostness, while Tait properness excludes shared endpoints.  Thus the
remaining case is exactly the cross-sector drainage pattern, rather than a
same-sector nested chord. -/
theorem other_chord_crosses_of_hasEndpointInside_innermost
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    {outer chord : OrderedPathChord (radial.path.length + 1)}
    (hinnermost : InnermostIn outer
      (majorityChordDiagram C majority first second radial))
    (houter : outer ∈
      majorityChordDiagram C majority first second radial)
    (hchord : chord ∈
      majorityChordDiagram C majority first second radial)
    (hne : chord ≠ outer)
    (htouches : chord.HasEndpointInside outer) :
    chord.Crosses outer := by
  exact OrderedPathChord.crosses_of_hasEndpointInside_of_innermost
    (majorityChordDiagram_pairwiseEndpointDisjoint C majority first second
      radial)
    hinnermost houter hchord hne htouches

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Correct source-facing drainage premise: once the rotation-system layer
supplies noncrossing and a chord is chosen innermost, no other third-color
same-path chord has an endpoint on its open subarc.  Endpoint disjointness is
not an extra geometric hypothesis; it was derived above from Tait
properness. -/
theorem no_other_endpoint_inside_innermost_chord
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (hnoncrossing : PairwiseNoncrossing
      (majorityChordDiagram C majority first second radial))
    {outer chord : OrderedPathChord (radial.path.length + 1)}
    (hinnermost : InnermostIn outer
      (majorityChordDiagram C majority first second radial))
    (houter : outer ∈ majorityChordDiagram C majority first second radial)
    (hchord : chord ∈ majorityChordDiagram C majority first second radial)
    (hne : chord ≠ outer) :
    ¬ chord.HasEndpointInside outer := by
  exact not_hasEndpointInside_of_innermost_of_pairwiseNoncrossing
    hnoncrossing
    (majorityChordDiagram_pairwiseEndpointDisjoint
      C majority first second radial)
    hinnermost houter hchord hne

end

end GoertzelV24ClosedWebRadialPathChordDiagram

end Mettapedia.GraphTheory.FourColor
