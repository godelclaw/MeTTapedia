import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChords
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleWalkTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile

/-!
# Oriented face-side transport around a closed-web chord cycle

Every edge endpoint of a same-path chord cycle lies strictly inside the
annular tangle and is therefore locally cubic.  Combining that fact with the
simple-cycle exhaustion lemma lets the exact-cut label propagate along the
selected oriented side of the whole chord-cycle dart chain.

This is still a transport theorem, not Sector Alternation: it identifies no
second chord and assumes no pairwise noncrossing property.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebChordCycleFaceSideTransport

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedBoundaryCounts
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance chordCycleFaceSideGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every based vertex occurring in the chord-cycle dart chain is locally
cubic, even though the framed annular graph has degree-one interface stubs. -/
theorem cycleWalk_dartsAt_card_eq_three
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (dart : G.Dart) (hdart : dart ∈ chord.cycleWalk.darts) :
    (embedded.RS.dartsAt (embedded.RS.vertOf dart)).card = 3 := by
  have hedge : dart.edge ∈ chord.cycleWalk.edges :=
    List.mem_map_of_mem hdart
  have hvertex : dart.fst ∈ (dart.edge : Sym2 V) := by
    simp [SimpleGraph.Dart.edge]
  have hincident :=
    chord.cycleWalk_edge_endpoint_incidentEdgeFinset_card_eq_three
      hdata htriple ⟨dart.edge, dart.edge_mem⟩ hedge hvertex
  change ({candidate : G.Dart | candidate.fst = dart.fst} :
    Finset G.Dart).card = 3
  rw [G.dart_fst_fiber_card_eq_degree]
  rw [← incidentEdgeFinset_card_eq_degree]
  exact hincident

/-!
At a vertex outside the chord wall, the cut facial component already gives a
well-defined primal side.  The only input beyond the generic face-tracing
lemma is the graph/rotation bridge from the radial chord module; no choice is
made at wall vertices here.
-/

theorem faceComponentSide_iff_of_vertex_off_cycleWalk_support
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)))
    {vertex : V} (anchor : embedded.RS.D)
    (hanchor : embedded.RS.vertOf anchor = vertex)
    (hvertex : vertex ∉ chord.cycleWalk.support) :
    faceComponentSide embedded.RS
        (chord.boundary htriple).wall seed vertex ↔
      (faceAdjacencyAvoiding
        (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        (chord.boundary htriple).wall).Reachable
        seed (orbitFaceVertex embedded.RS anchor) := by
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  apply faceComponentSide_iff_of_anchor_of_vertex_avoids
    embedded.RS htwoSided hrotation (chord.boundary htriple).wall
      seed vertex anchor hanchor
  intro dart hdart
  have hnotCycle := chord.toRotationSystem_all_incident_edges_not_mem_cycleWalk_of_vertex_not_mem_support
    embedded.cellulation.rotation hvertex dart hdart
  intro hwall
  apply hnotCycle
  exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple
    (embedded.RS.edgeOf dart)).1 hwall

/-!
The vertex statement upgrades to an edge statement away from the wall.  This
is the exact non-crossing classification for the easy class of ambient edges:
both endpoint rotation fibers avoid the cycle, so the cut facial component is
constant across the edge.
-/

theorem faceComponentSide_iff_of_edge_off_cycleWalk_support
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)))
    (dart : embedded.RS.D)
    (hleft : embedded.RS.vertOf dart ∉ chord.cycleWalk.support)
    (hright : embedded.RS.vertOf (embedded.RS.alpha dart) ∉
      chord.cycleWalk.support) :
    faceComponentSide embedded.RS
        (chord.boundary htriple).wall seed (embedded.RS.vertOf dart) ↔
      faceComponentSide embedded.RS
        (chord.boundary htriple).wall seed
          (embedded.RS.vertOf (embedded.RS.alpha dart)) := by
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have haway : embedded.RS.edgeOf dart ∉
      (chord.boundary htriple).wall := by
    intro hwall
    have hcycle : (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges :=
      (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple
        (embedded.RS.edgeOf dart)).1 hwall
    exact hleft (chord.cycleWalk.mem_support_of_mem_edges hcycle (by
      change dart.fst ∈ dart.edge
      simp [SimpleGraph.Dart.edge]))
  apply faceComponentSide_iff_of_nonwall_edge
      embedded.RS htwoSided hrotation (chord.boundary htriple).wall seed dart
      haway
  · intro incident hincident hwall
    apply chord.toRotationSystem_edge_not_mem_cycleWalk_of_vertex_not_mem_support
      embedded.cellulation.rotation hleft incident hincident
    exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple
      (embedded.RS.edgeOf incident)).1 hwall
  · intro incident hincident hwall
    apply chord.toRotationSystem_edge_not_mem_cycleWalk_of_vertex_not_mem_support
      embedded.cellulation.rotation hright incident hincident
    exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple
      (embedded.RS.edgeOf incident)).1 hwall

/-!
The preceding theorem is deliberately an off-wall statement.  The following
constructor records exactly how far it can be pushed toward the primal
separator: if a proposed ambient side agrees with the facial component away
from the chord wall, then all unlisted edges whose two endpoints avoid the
wall are handled automatically.  The only remaining local geometric input is
the `wallDartSideSeam` clause for an unlisted edge touching the wall.  This is
the precise vertex-side/Jordan seam, rather than a hidden strengthening of
face-component existential data.
-/

noncomputable def cyclicEdgeCutRealization_of_faceComponentSide_with_wallDartSideSeam
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)))
    {edgeCut : Finset G.edgeSet} (side : V → Prop)
    (hside_off : ∀ (vertex : V),
      vertex ∉ chord.cycleWalk.support →
        (side vertex ↔
          faceComponentSide embedded.RS
            (chord.boundary htriple).wall seed vertex))
    (wallDartSideSeam : ∀ (edge : G.edgeSet), edge ∉ edgeCut →
      ∀ (dart : embedded.RS.D), embedded.RS.edgeOf dart = edge →
        (embedded.RS.vertOf dart ∈ chord.cycleWalk.support ∨
          embedded.RS.vertOf (embedded.RS.alpha dart) ∈
            chord.cycleWalk.support) →
        (side (embedded.RS.vertOf dart) ↔
          side (embedded.RS.vertOf (embedded.RS.alpha dart))))
    (hcut_crosses : ∀ edge : G.edgeSet, edge ∈ edgeCut →
      EdgeCrossesVertexSide G side edge)
    (hinside_cycle : HasCycleOnSide G side)
    (houtside_cycle : HasCycleOnSide G (fun vertex => ¬ side vertex)) :
    CyclicEdgeCutRealization G edgeCut := by
  refine CyclicEdgeCutRealization.of_edge_side_classification side hcut_crosses ?_
    hinside_cycle houtside_cycle
  intro edge hedge u v hu hv
  obtain ⟨dart, hdart⟩ := embedded.RS.dartsOn_nonempty edge
  have hdartEndpoints :
      embedded.RS.endpoints edge =
        {embedded.RS.vertOf dart,
          embedded.RS.vertOf (embedded.RS.alpha dart)} :=
    embedded.RS.endpoints_eq_pair_of_mem hdart
  have huEndpoints : u ∈ embedded.RS.endpoints edge := by
    exact (mem_simpleGraphRotationSystem_endpoints_iff
      embedded.cellulation.rotation edge u).2 hu
  have hvEndpoints : v ∈ embedded.RS.endpoints edge := by
    exact (mem_simpleGraphRotationSystem_endpoints_iff
      embedded.cellulation.rotation edge v).2 hv
  have huCases :
      u = embedded.RS.vertOf dart ∨
        u = embedded.RS.vertOf (embedded.RS.alpha dart) := by
    rw [hdartEndpoints] at huEndpoints
    simpa using huEndpoints
  have hvCases :
      v = embedded.RS.vertOf dart ∨
        v = embedded.RS.vertOf (embedded.RS.alpha dart) := by
    rw [hdartEndpoints] at hvEndpoints
    simpa using hvEndpoints
  by_cases hleftWall :
      embedded.RS.vertOf dart ∈ chord.cycleWalk.support
  · have hsideDart :
        side (embedded.RS.vertOf dart) ↔
          side (embedded.RS.vertOf (embedded.RS.alpha dart)) := by
      exact (wallDartSideSeam edge hedge dart
        (embedded.RS.mem_dartsOn.mp hdart)) (Or.inl hleftWall)
    rcases huCases with huD | huA <;>
      rcases hvCases with hvD | hvA
    · simpa [huD, hvD] using hsideDart
    · simpa [huD, hvA] using hsideDart
    · simpa [huA, hvD] using hsideDart.symm
    · simpa [huA, hvA] using hsideDart.symm
  by_cases hrightWall :
      embedded.RS.vertOf (embedded.RS.alpha dart) ∈
        chord.cycleWalk.support
  · have hsideDart :
        side (embedded.RS.vertOf dart) ↔
          side (embedded.RS.vertOf (embedded.RS.alpha dart)) := by
      exact (wallDartSideSeam edge hedge dart
        (embedded.RS.mem_dartsOn.mp hdart)) (Or.inr hrightWall)
    rcases huCases with huD | huA <;>
      rcases hvCases with hvD | hvA
    · simpa [huD, hvD] using hsideDart
    · simpa [huD, hvA] using hsideDart
    · simpa [huA, hvD] using hsideDart.symm
    · simpa [huA, hvA] using hsideDart.symm
  have hface := faceComponentSide_iff_of_edge_off_cycleWalk_support
    embedded chord htriple htwoSided seed dart hleftWall hrightWall
  have hsideLeft :
      side (embedded.RS.vertOf dart) ↔
        faceComponentSide embedded.RS
          (chord.boundary htriple).wall seed
          (embedded.RS.vertOf dart) := by
    have hside := hside_off (embedded.RS.vertOf dart)
    exact hside hleftWall
  have hsideRight :
      side (embedded.RS.vertOf (embedded.RS.alpha dart)) ↔
        faceComponentSide embedded.RS
          (chord.boundary htriple).wall seed
          (embedded.RS.vertOf (embedded.RS.alpha dart)) := by
    have hside := hside_off
      (embedded.RS.vertOf (embedded.RS.alpha dart))
    exact hside hrightWall
  have hsideDart :
      side (embedded.RS.vertOf dart) ↔
        side (embedded.RS.vertOf (embedded.RS.alpha dart)) :=
    hsideLeft.trans (hface.trans hsideRight.symm)
  rcases huCases with huD | huA <;>
    rcases hvCases with hvD | hvA
  · simpa [huD, hvD] using hsideDart
  · simpa [huD, hvA] using hsideDart
  · simpa [huA, hvD] using hsideDart.symm
  · simpa [huA, hvA] using hsideDart.symm

/-- Every edge incident to a radial-path position strictly outside a chord's
closed endpoint interval avoids that chord cycle.  Simplicity of the radial
path rules out a second occurrence of the same endpoint inside the interval. -/
theorem incidentEdge_not_mem_cycleWalk_of_position_outside
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (position : Nat) (hposition : position ≤ radial.path.length)
    (houtside : position < chord.left.val ∨
      chord.right.val < position)
    (edge : G.edgeSet)
    (hincident :
      (ambientRadialPath radial).getVert position ∈ (edge.1 : Sym2 V)) :
    edge.1 ∉ chord.cycleWalk.edges := by
  intro hedge
  rcases chord.exists_position_between_of_mem_cycleWalk_edges
      htriple edge hedge hincident with
    ⟨inside, hleft, hright, hinside⟩
  have hinsideBound : inside ≤ radial.path.length := by
    have hrightBound := chord.right.isLt
    omega
  have hpositions : inside = position :=
    (ambientRadialPath_isPath radial).getVert_injOn
      (by simpa [ambientRadialPath_length] using hinsideBound)
      (by simpa [ambientRadialPath_length] using hposition)
      hinside
  rcases houtside with hbefore | hafter <;> omega

/-- The exact cut of a same-path chord cycle carries one constant label along
the cycle's oriented dart side.  Local cubicity is derived from annular
well-formedness at the actual cycle vertices. -/
theorem labels_eq_firstDart_lastDart_of_exact_chordCycle_cut
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    {A : Type*} (labels : OrbitFace embedded.RS → A)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges) :
    labels (dartOrbitFace embedded.RS
        (chord.cycleWalk.firstDart
          (chord.cycleWalk_isCycle htriple).not_nil)) =
      labels (dartOrbitFace embedded.RS
        (chord.cycleWalk.lastDart
          (chord.cycleWalk_isCycle htriple).not_nil)) := by
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  apply embedded.cellulation.rotation
    |>.cycle_labels_eq_firstDart_lastDart_of_local_cubic
      hrotation labels chord.cycleWalk hcycle hexact
  intro dart hdart
  exact cycleWalk_dartsAt_card_eq_three embedded hdata chord htriple
    dart hdart

/-- The same exact chord-cycle cut carries the first oriented side label to
every actual dart in the cycle chain. -/
theorem labels_eq_firstDart_dart_of_mem_exact_chordCycle_cut
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    {A : Type*} (labels : OrbitFace embedded.RS → A)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (target : G.Dart) (htarget : target ∈ chord.cycleWalk.darts) :
    labels (dartOrbitFace embedded.RS
        (chord.cycleWalk.firstDart
          (chord.cycleWalk_isCycle htriple).not_nil)) =
      labels (dartOrbitFace embedded.RS target) := by
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  apply embedded.cellulation.rotation
    |>.cycle_labels_eq_firstDart_dart_of_mem_darts_of_local_cubic
      hrotation labels chord.cycleWalk hcycle hexact
        (cycleWalk_dartsAt_card_eq_three
          embedded hdata chord htriple) target htarget

end

end GoertzelV24ClosedWebChordCycleFaceSideTransport

end Mettapedia.GraphTheory.FourColor
