import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChords
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFaceComponentCycleTransport
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
open GoertzelV24ClosedWebFaceComponentCycleTransport
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

/-! A consecutive pair in the simple chord cycle supplies the two wall darts
at its common cubic vertex.  Therefore an explicitly off-wall external dart
is the unique third dart in that fiber, and every other incident dart is on
the wall.  This is the local incidence construction needed by the primal
side/Jordan seam; it is stronger than merely assuming an adjacent rotational
successor. -/

theorem all_other_incident_edges_in_wall_of_chord_cycle_turn
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (hdata : data.WellFormed)
    {previous cycleDart : embedded.RS.D}
    (hprevious : previous ∈ chord.cycleWalk.darts)
    (hcycleDart : cycleDart ∈ chord.cycleWalk.darts)
    (hbase : embedded.RS.vertOf cycleDart =
      embedded.RS.vertOf (embedded.RS.alpha previous))
    (hnonback : embedded.RS.alpha previous ≠ cycleDart)
    (external : embedded.RS.D)
    (hexternalVertex : embedded.RS.vertOf external =
      embedded.RS.vertOf cycleDart)
    (haway : embedded.RS.edgeOf external ∉
      (chord.boundary htriple).wall) :
    ∀ dart : embedded.RS.D,
      embedded.RS.vertOf dart = embedded.RS.vertOf external →
      dart ≠ external →
      embedded.RS.edgeOf dart ∈ (chord.boundary htriple).wall := by
  have hcard := cycleWalk_dartsAt_card_eq_three
    embedded hdata chord htriple cycleDart hcycleDart
  have hcycleBase : embedded.RS.vertOf cycleDart =
      embedded.RS.vertOf external := by
    simpa using hexternalVertex.symm
  have hpreviousEdge : (embedded.RS.edgeOf previous).1 ∈
      chord.cycleWalk.edges := by
    change previous.edge ∈ chord.cycleWalk.edges
    exact List.mem_map_of_mem hprevious
  have hcycleEdge : (embedded.RS.edgeOf cycleDart).1 ∈
      chord.cycleWalk.edges := by
    change cycleDart.edge ∈ chord.cycleWalk.edges
    exact List.mem_map_of_mem hcycleDart
  have hwallPrevious : embedded.RS.edgeOf (embedded.RS.alpha previous) ∈
      (chord.boundary htriple).wall := by
    rw [chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple]
    simpa using hpreviousEdge
  have hwallCycleDart : embedded.RS.edgeOf cycleDart ∈
      (chord.boundary htriple).wall := by
    rw [chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple]
    simpa using hcycleEdge
  have hpreviousNeExternal : embedded.RS.alpha previous ≠ external := by
    intro heq
    apply haway
    rw [← heq]
    exact hwallPrevious
  have hcycleDartNeExternal : cycleDart ≠ external := by
    intro heq
    apply haway
    rw [← heq]
    exact hwallCycleDart
  have htripleSubset :
      ({embedded.RS.alpha previous, cycleDart, external} :
        Finset embedded.RS.D) ⊆
      embedded.RS.dartsAt (embedded.RS.vertOf external) := by
    intro dart hdart
    rcases Finset.mem_insert.mp hdart with hdart | hdart
    · subst dart
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hbase.symm.trans hcycleBase⟩
    rcases Finset.mem_insert.mp hdart with hdart | hdart
    · subst dart
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcycleBase⟩
    have hdartEq : dart = external := Finset.mem_singleton.mp hdart
    subst dart
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hprevNotMem : embedded.RS.alpha previous ∉
      ({cycleDart, external} : Finset embedded.RS.D) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with hmem | hmem
    · exact hnonback hmem
    · exact hpreviousNeExternal (Finset.mem_singleton.mp hmem)
  have hcycleNotMem : cycleDart ∉
      ({external} : Finset embedded.RS.D) := by
    exact fun h => hcycleDartNeExternal (Finset.mem_singleton.mp h)
  have htripleCard :
      ({embedded.RS.alpha previous, cycleDart, external} :
        Finset embedded.RS.D).card = 3 := by
    rw [Finset.card_insert_of_notMem hprevNotMem]
    rw [Finset.card_insert_of_notMem hcycleNotMem]
    simp
  have hcardExternal :
      (embedded.RS.dartsAt (embedded.RS.vertOf external)).card = 3 := by
    rw [← hcycleBase]
    exact hcard
  have htripleEq :
      ({embedded.RS.alpha previous, cycleDart, external} :
        Finset embedded.RS.D) =
      embedded.RS.dartsAt (embedded.RS.vertOf external) := by
    apply Finset.eq_of_subset_of_card_le htripleSubset
    rw [hcardExternal, htripleCard]
  intro dart hdartBase hdartNeExternal
  have hdartMem : dart ∈ embedded.RS.dartsAt (embedded.RS.vertOf external) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdartBase⟩
  rw [← htripleEq] at hdartMem
  rcases Finset.mem_insert.mp hdartMem with hpreviousDart | hdartMem
  · rw [hpreviousDart]
    exact hwallPrevious
  rcases Finset.mem_insert.mp hdartMem with hcycleDart' | hexternalDart
  · rw [hcycleDart']
    exact hwallCycleDart
  exact False.elim (hdartNeExternal (Finset.mem_singleton.mp hexternalDart))

/-! The generic cubic seam is now exposed at the actual chord interface.  A
cycle dart supplies the local degree-three certificate; the caller still has
to provide the exact-cut labels and identify which rotational successor edge
is on the chord wall.  This is plumbing, not a hidden Jordan assumption. -/

theorem faceAdjacencyAvoiding_reachable_of_same_exact_chordCycle_label_at_cycle_vertex
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (cycleDart : embedded.RS.D)
    (hcycleDart : cycleDart ∈ chord.cycleWalk.darts)
    (external : embedded.RS.D)
    (hexternalVertex : embedded.RS.vertOf external =
      embedded.RS.vertOf cycleDart)
    (haway : embedded.RS.edgeOf external ∉
      (chord.boundary htriple).wall)
    (hadjacent :
      embedded.RS.edgeOf (embedded.RS.rho external) ∈
          (chord.boundary htriple).wall ∨
        embedded.RS.edgeOf (embedded.RS.rho (embedded.RS.rho external)) ∈
          (chord.boundary htriple).wall)
    {incident : embedded.RS.D}
    (hincident : embedded.RS.vertOf incident =
      embedded.RS.vertOf external)
    (hsame : labels (dartOrbitFace embedded.RS incident) =
      labels (dartOrbitFace embedded.RS external)) :
    (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Reachable
      (orbitFaceVertex embedded.RS external)
      (orbitFaceVertex embedded.RS incident) := by
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hcardCycle := cycleWalk_dartsAt_card_eq_three
    embedded hdata chord htriple cycleDart hcycleDart
  have hcardExternal :
      (embedded.RS.dartsAt (embedded.RS.vertOf external)).card = 3 := by
    rw [hexternalVertex]
    exact hcardCycle
  have hexactWall : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        embedded.RS.edgeOf dart ∈ (chord.boundary htriple).wall := by
    intro dart
    rw [chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple]
    exact hexact dart
  exact faceAdjacencyAvoiding_reachable_of_same_exact_label_at_cubic_vertex_of_adjacent_wall
    embedded.RS htwoSided hrotation (chord.boundary htriple).wall labels
      hexactWall external hcardExternal haway hadjacent hincident hsame

/-! The preceding interface exposed the final rotational disjunction.  This
adapter exposes the more geometric premise instead: once every other dart in
the cubic fiber is known to be a wall dart, the disjunction is automatic.
The remaining proof obligation is therefore visibly the local primal
side/Jordan construction, not an arbitrary face-label choice. -/

theorem faceAdjacencyAvoiding_reachable_of_same_exact_chordCycle_label_at_cycle_vertex_of_all_other_incident_edges_in_wall
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (cycleDart : embedded.RS.D)
    (hcycleDart : cycleDart ∈ chord.cycleWalk.darts)
    (external : embedded.RS.D)
    (hexternalVertex : embedded.RS.vertOf external =
      embedded.RS.vertOf cycleDart)
    (haway : embedded.RS.edgeOf external ∉
      (chord.boundary htriple).wall)
    (hother : ∀ dart : embedded.RS.D,
      embedded.RS.vertOf dart = embedded.RS.vertOf external →
      dart ≠ external →
      embedded.RS.edgeOf dart ∈ (chord.boundary htriple).wall)
    {incident : embedded.RS.D}
    (hincident : embedded.RS.vertOf incident =
      embedded.RS.vertOf external)
    (hsame : labels (dartOrbitFace embedded.RS incident) =
      labels (dartOrbitFace embedded.RS external)) :
    (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Reachable
      (orbitFaceVertex embedded.RS external)
      (orbitFaceVertex embedded.RS incident) := by
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hcardCycle := cycleWalk_dartsAt_card_eq_three
    embedded hdata chord htriple cycleDart hcycleDart
  have hcardExternal :
      (embedded.RS.dartsAt (embedded.RS.vertOf external)).card = 3 := by
    rw [hexternalVertex]
    exact hcardCycle
  have hexactWall : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        embedded.RS.edgeOf dart ∈ (chord.boundary htriple).wall := by
    intro dart
    rw [chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple]
    exact hexact dart
  exact faceAdjacencyAvoiding_reachable_of_same_exact_label_at_cubic_vertex_of_all_other_incident_edges_in_wall
    embedded.RS htwoSided hrotation (chord.boundary htriple).wall labels
      hexactWall external hcardExternal haway hother hincident hsame

/-! A consecutive cycle turn now discharges the local incidence premise
itself.  Thus the face-side connection can be invoked directly from the
ordinary cycle-list data (two adjacent wall darts, cubicity, and an external
off-wall dart), with no manually supplied rotational successor case. -/

theorem faceAdjacencyAvoiding_reachable_of_same_exact_chordCycle_label_at_cycle_turn
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {previous cycleDart : embedded.RS.D}
    (hprevious : previous ∈ chord.cycleWalk.darts)
    (hcycleDart : cycleDart ∈ chord.cycleWalk.darts)
    (hbase : embedded.RS.vertOf cycleDart =
      embedded.RS.vertOf (embedded.RS.alpha previous))
    (hnonback : embedded.RS.alpha previous ≠ cycleDart)
    (external : embedded.RS.D)
    (hexternalVertex : embedded.RS.vertOf external =
      embedded.RS.vertOf cycleDart)
    (haway : embedded.RS.edgeOf external ∉
      (chord.boundary htriple).wall)
    {incident : embedded.RS.D}
    (hincident : embedded.RS.vertOf incident =
      embedded.RS.vertOf external)
    (hsame : labels (dartOrbitFace embedded.RS incident) =
      labels (dartOrbitFace embedded.RS external)) :
    (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Reachable
      (orbitFaceVertex embedded.RS external)
      (orbitFaceVertex embedded.RS incident) := by
  exact faceAdjacencyAvoiding_reachable_of_same_exact_chordCycle_label_at_cycle_vertex_of_all_other_incident_edges_in_wall
    embedded hdata chord htriple htwoSided labels hexact cycleDart hcycleDart
      external hexternalVertex haway
      (all_other_incident_edges_in_wall_of_chord_cycle_turn
        embedded chord htriple hdata hprevious hcycleDart hbase hnonback
          external hexternalVertex haway)
      hincident hsame

/-! Convenience form for the existing `FaceCutCycleTurnStep` chain: its
first two fields are exactly the base-point and nonbacktracking hypotheses
used above. -/

theorem faceAdjacencyAvoiding_reachable_of_same_exact_chordCycle_label_at_faceCutCycleTurn
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {previous cycleDart : embedded.RS.D}
    (hprevious : previous ∈ chord.cycleWalk.darts)
    (hcycleDart : cycleDart ∈ chord.cycleWalk.darts)
    (hturn : embedded.RS.FaceCutCycleTurnStep
      (fun edge => edge ∈ (chord.boundary htriple).wall)
      previous cycleDart)
    (external : embedded.RS.D)
    (hexternalVertex : embedded.RS.vertOf external =
      embedded.RS.vertOf cycleDart)
    (haway : embedded.RS.edgeOf external ∉
      (chord.boundary htriple).wall)
    {incident : embedded.RS.D}
    (hincident : embedded.RS.vertOf incident =
      embedded.RS.vertOf external)
    (hsame : labels (dartOrbitFace embedded.RS incident) =
      labels (dartOrbitFace embedded.RS external)) :
    (faceAdjacencyAvoiding
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))
      (chord.boundary htriple).wall).Reachable
      (orbitFaceVertex embedded.RS external)
      (orbitFaceVertex embedded.RS incident) := by
  exact faceAdjacencyAvoiding_reachable_of_same_exact_chordCycle_label_at_cycle_turn
    embedded hdata chord htriple htwoSided labels hexact hprevious hcycleDart
      hturn.1 hturn.2.1 external hexternalVertex haway hincident hsame

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

/-!
The generic constructor above accepts a proposed ambient side so that it can
be reused by other annulus layers.  For the closed-web chord itself there is
no reason to leave that field abstract: away from the wall the canonical
predicate is exactly `faceComponentSide`.  This specialization removes that
artificial parameter and exposes the true remaining geometric obligations.
-/

noncomputable def cyclicEdgeCutRealization_of_faceComponentSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)))
    {edgeCut : Finset G.edgeSet}
    (wallDartSideSeam : ∀ (edge : G.edgeSet), edge ∉ edgeCut →
      ∀ (dart : embedded.RS.D), embedded.RS.edgeOf dart = edge →
        (embedded.RS.vertOf dart ∈ chord.cycleWalk.support ∨
          embedded.RS.vertOf (embedded.RS.alpha dart) ∈
            chord.cycleWalk.support) →
        (faceComponentSide embedded.RS (chord.boundary htriple).wall seed
            (embedded.RS.vertOf dart) ↔
          faceComponentSide embedded.RS (chord.boundary htriple).wall seed
            (embedded.RS.vertOf (embedded.RS.alpha dart))))
    (hcut_crosses : ∀ edge : G.edgeSet, edge ∈ edgeCut →
      EdgeCrossesVertexSide G
        (faceComponentSide embedded.RS (chord.boundary htriple).wall seed)
        edge)
    (hinside_cycle : HasCycleOnSide G
      (faceComponentSide embedded.RS (chord.boundary htriple).wall seed))
    (houtside_cycle : HasCycleOnSide G
      (fun vertex => ¬ faceComponentSide embedded.RS
        (chord.boundary htriple).wall seed vertex)) :
    CyclicEdgeCutRealization G edgeCut := by
  exact cyclicEdgeCutRealization_of_faceComponentSide_with_wallDartSideSeam
    embedded chord htriple htwoSided seed
    (fun vertex => faceComponentSide embedded.RS
      (chord.boundary htriple).wall seed vertex)
    (fun _vertex _hoffWall => Iff.rfl)
    wallDartSideSeam hcut_crosses hinside_cycle houtside_cycle

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
