import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialPathChords
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFaceComponentCycleTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleWalkTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphFaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationVertexCutProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutVertexAvoidingTransport

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

/-!
The final primal side should fill the selected facial component across the
wall vertices, rather than use the existential component predicate there.
This definition makes that normal-form choice explicit.  The only new input
needed for an unlisted edge touching the wall is that its off-wall endpoint
belongs to the selected component; edges with both endpoints off the wall use
the already-proved facial transport.
-/

def filledFaceComponentSide
    (support : List V) (faceSide : V → Prop) (vertex : V) : Prop :=
  vertex ∈ support ∨ faceSide vertex

theorem filledFaceComponentSide_iff_of_not_mem
    {support : List V} {faceSide : V → Prop} {vertex : V}
    (hvertex : vertex ∉ support) :
    filledFaceComponentSide support faceSide vertex ↔ faceSide vertex := by
  simp [filledFaceComponentSide, hvertex]

/-! A port-reachability form of the remaining support seam.  If a non-wall
edge leaves the chord support, it is enough to route the facial orbit of its
off-support port back to the selected seed.  The endpoint theorem below then
turns that route into membership in the selected component. -/

theorem faceComponentSide_of_off_cycleWalk_endpoint_of_seed_reaches_dart
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
    (haway : embedded.RS.edgeOf dart ∉
      (chord.boundary htriple).wall)
    (hoff : embedded.RS.vertOf (embedded.RS.alpha dart) ∉
      chord.cycleWalk.support)
    (hseed :
      (faceAdjacencyAvoiding
        (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        (chord.boundary htriple).wall).Reachable
        seed (orbitFaceVertex embedded.RS dart)) :
    faceComponentSide embedded.RS (chord.boundary htriple).wall seed
      (embedded.RS.vertOf (embedded.RS.alpha dart)) := by
  rw [faceComponentSide_iff_of_vertex_off_cycleWalk_support
    embedded chord htriple htwoSided seed (embedded.RS.alpha dart) rfl hoff]
  exact hseed.trans
    (faceAdjacencyAvoiding_reachable_of_alpha
      embedded.RS htwoSided (chord.boundary htriple).wall dart haway)

/-! The support seam can therefore be stated without an existential side
predicate.  This is the useful interface for a later annulus/Jordan proof:
only the two oriented off-support port routes are geometric input. -/

theorem filledFaceComponentSide_wallDartSideSeam_of_externalPortReachability
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
    (hreach : ∀ (edge : G.edgeSet), edge ∉
      edgeCut →
      ∀ (dart : embedded.RS.D), embedded.RS.edgeOf dart = edge →
      ((embedded.RS.vertOf dart ∈ chord.cycleWalk.support →
          embedded.RS.vertOf (embedded.RS.alpha dart) ∉
            chord.cycleWalk.support →
          (faceAdjacencyAvoiding
            (orbitFaceBoundary embedded.RS)
            (Finset.univ : Finset (OrbitFace embedded.RS))
            (chord.boundary htriple).wall).Reachable
            seed (orbitFaceVertex embedded.RS
              (embedded.RS.alpha dart))) ∧
       (embedded.RS.vertOf (embedded.RS.alpha dart) ∈
          chord.cycleWalk.support →
          embedded.RS.vertOf dart ∉ chord.cycleWalk.support →
          (faceAdjacencyAvoiding
            (orbitFaceBoundary embedded.RS)
            (Finset.univ : Finset (OrbitFace embedded.RS))
            (chord.boundary htriple).wall).Reachable
            seed (orbitFaceVertex embedded.RS dart)))) :
    ∀ (edge : G.edgeSet), edge ∉ edgeCut →
      ∀ (dart : embedded.RS.D), embedded.RS.edgeOf dart = edge →
      (embedded.RS.vertOf dart ∈ chord.cycleWalk.support ∨
        embedded.RS.vertOf (embedded.RS.alpha dart) ∈
          chord.cycleWalk.support) →
      (filledFaceComponentSide chord.cycleWalk.support
          (faceComponentSide embedded.RS
            (chord.boundary htriple).wall seed)
          (embedded.RS.vertOf dart) ↔
       filledFaceComponentSide chord.cycleWalk.support
          (faceComponentSide embedded.RS
            (chord.boundary htriple).wall seed)
          (embedded.RS.vertOf (embedded.RS.alpha dart))) := by
  intro edge hedge dart hdart htouch
  by_cases hleft : embedded.RS.vertOf dart ∈ chord.cycleWalk.support
  · by_cases hright : embedded.RS.vertOf (embedded.RS.alpha dart) ∈
        chord.cycleWalk.support
    · change dart.fst ∈ chord.cycleWalk.support at hleft
      change dart.snd ∈ chord.cycleWalk.support at hright
      simp [filledFaceComponentSide, hleft, hright]
    · change dart.fst ∈ chord.cycleWalk.support at hleft
      change dart.snd ∉ chord.cycleWalk.support at hright
      have hrightSide : faceComponentSide embedded.RS
          (chord.boundary htriple).wall seed dart.snd := by
        change faceComponentSide embedded.RS
          (chord.boundary htriple).wall seed
          (embedded.RS.vertOf (embedded.RS.alpha dart))
        rw [faceComponentSide_iff_of_vertex_off_cycleWalk_support
          embedded chord htriple htwoSided seed
          (embedded.RS.alpha dart) rfl hright]
        exact (hreach edge hedge dart hdart).1 hleft hright
      simp [filledFaceComponentSide, hleft, hright, hrightSide]
  · have hright : embedded.RS.vertOf (embedded.RS.alpha dart) ∈
      chord.cycleWalk.support := by
      exact htouch.resolve_left hleft
    change dart.fst ∉ chord.cycleWalk.support at hleft
    change dart.snd ∈ chord.cycleWalk.support at hright
    have hleftSide : faceComponentSide embedded.RS
        (chord.boundary htriple).wall seed dart.fst := by
      change faceComponentSide embedded.RS
        (chord.boundary htriple).wall seed
        (embedded.RS.vertOf dart)
      rw [faceComponentSide_iff_of_vertex_off_cycleWalk_support
        embedded chord htriple htwoSided seed dart rfl hleft]
      exact (hreach edge hedge dart hdart).2 hright hleft
    simp [filledFaceComponentSide, hleft, hright, hleftSide]

noncomputable def cyclicEdgeCutRealization_of_filledFaceComponentSide
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
    (hsupport_seam : ∀ (edge : G.edgeSet), edge ∉ edgeCut →
      ∀ (dart : embedded.RS.D), embedded.RS.edgeOf dart = edge →
      ((embedded.RS.vertOf dart ∈ chord.cycleWalk.support →
          embedded.RS.vertOf (embedded.RS.alpha dart) ∉
            chord.cycleWalk.support →
          faceComponentSide embedded.RS (chord.boundary htriple).wall
            seed (embedded.RS.vertOf (embedded.RS.alpha dart))) ∧
       (embedded.RS.vertOf (embedded.RS.alpha dart) ∈
          chord.cycleWalk.support →
          embedded.RS.vertOf dart ∉ chord.cycleWalk.support →
          faceComponentSide embedded.RS (chord.boundary htriple).wall
            seed (embedded.RS.vertOf dart))))
    (hcut_crosses : ∀ edge : G.edgeSet, edge ∈ edgeCut →
      EdgeCrossesVertexSide G
        (filledFaceComponentSide chord.cycleWalk.support
          (faceComponentSide embedded.RS (chord.boundary htriple).wall seed))
        edge)
    (hinside_cycle : HasCycleOnSide G
      (filledFaceComponentSide chord.cycleWalk.support
        (faceComponentSide embedded.RS (chord.boundary htriple).wall seed)))
    (houtside_cycle : HasCycleOnSide G
      (fun vertex => ¬ filledFaceComponentSide chord.cycleWalk.support
        (faceComponentSide embedded.RS (chord.boundary htriple).wall seed)
          vertex)) :
    CyclicEdgeCutRealization G edgeCut := by
  let side : V → Prop := filledFaceComponentSide chord.cycleWalk.support
    (faceComponentSide embedded.RS (chord.boundary htriple).wall seed)
  apply cyclicEdgeCutRealization_of_faceComponentSide_with_wallDartSideSeam
    embedded chord htriple htwoSided seed side
  · intro vertex hvertex
    exact filledFaceComponentSide_iff_of_not_mem hvertex
  · intro edge hedge dart hdart htouch
    by_cases hleft : embedded.RS.vertOf dart ∈ chord.cycleWalk.support
    · by_cases hright : embedded.RS.vertOf (embedded.RS.alpha dart) ∈
          chord.cycleWalk.support
      · change dart.fst ∈ chord.cycleWalk.support at hleft
        change dart.snd ∈ chord.cycleWalk.support at hright
        simp [side, filledFaceComponentSide, hleft, hright]
      · have hrightSide := (hsupport_seam edge hedge dart hdart).1 hleft hright
        change dart.fst ∈ chord.cycleWalk.support at hleft
        change dart.snd ∉ chord.cycleWalk.support at hright
        change faceComponentSide embedded.RS (chord.boundary htriple).wall
          seed dart.snd at hrightSide
        simp [side, filledFaceComponentSide, hleft, hright, hrightSide]
    · by_cases hright : embedded.RS.vertOf (embedded.RS.alpha dart) ∈
          chord.cycleWalk.support
      · have hleftSide := (hsupport_seam edge hedge dart hdart).2 hright hleft
        change dart.fst ∉ chord.cycleWalk.support at hleft
        change dart.snd ∈ chord.cycleWalk.support at hright
        change faceComponentSide embedded.RS (chord.boundary htriple).wall
          seed dart.fst at hleftSide
        simp [side, filledFaceComponentSide, hleft, hright, hleftSide]
      · have hface := faceComponentSide_iff_of_edge_off_cycleWalk_support
          embedded chord htriple htwoSided seed dart hleft hright
        change dart.fst ∉ chord.cycleWalk.support at hleft
        change dart.snd ∉ chord.cycleWalk.support at hright
        simpa [side, filledFaceComponentSide, hleft, hright] using hface
  · exact hcut_crosses
  · exact hinside_cycle
  · exact houtside_cycle

/-! The route-facing constructor takes the port routes directly.  The generic
filled-side constructor still owns the mechanical endpoint classification;
this adapter only converts the route-level side equivalence into its
off-support component-membership seam. -/

noncomputable def cyclicEdgeCutRealization_of_filledFaceComponentSide_of_externalPortReachability
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
    (hreach : ∀ (edge : G.edgeSet), edge ∉ edgeCut →
      ∀ (dart : embedded.RS.D), embedded.RS.edgeOf dart = edge →
      ((embedded.RS.vertOf dart ∈ chord.cycleWalk.support →
          embedded.RS.vertOf (embedded.RS.alpha dart) ∉
            chord.cycleWalk.support →
          (faceAdjacencyAvoiding
            (orbitFaceBoundary embedded.RS)
            (Finset.univ : Finset (OrbitFace embedded.RS))
            (chord.boundary htriple).wall).Reachable
            seed (orbitFaceVertex embedded.RS
              (embedded.RS.alpha dart))) ∧
       (embedded.RS.vertOf (embedded.RS.alpha dart) ∈
          chord.cycleWalk.support →
          embedded.RS.vertOf dart ∉ chord.cycleWalk.support →
          (faceAdjacencyAvoiding
            (orbitFaceBoundary embedded.RS)
            (Finset.univ : Finset (OrbitFace embedded.RS))
            (chord.boundary htriple).wall).Reachable
            seed (orbitFaceVertex embedded.RS dart))))
    (hcut_crosses : ∀ edge : G.edgeSet, edge ∈ edgeCut →
      EdgeCrossesVertexSide G
        (filledFaceComponentSide chord.cycleWalk.support
          (faceComponentSide embedded.RS (chord.boundary htriple).wall seed))
        edge)
    (hinside_cycle : HasCycleOnSide G
      (filledFaceComponentSide chord.cycleWalk.support
        (faceComponentSide embedded.RS (chord.boundary htriple).wall seed)))
    (houtside_cycle : HasCycleOnSide G
      (fun vertex => ¬ filledFaceComponentSide chord.cycleWalk.support
        (faceComponentSide embedded.RS (chord.boundary htriple).wall seed)
          vertex)) :
    CyclicEdgeCutRealization G edgeCut := by
  have hsideSeam :=
    filledFaceComponentSide_wallDartSideSeam_of_externalPortReachability
      (edgeCut := edgeCut) embedded chord htriple htwoSided seed hreach
  refine cyclicEdgeCutRealization_of_filledFaceComponentSide
    (edgeCut := edgeCut) embedded chord htriple htwoSided seed ?_
    hcut_crosses hinside_cycle houtside_cycle
  intro edge hedge dart hdart
  constructor
  · intro hleft hright
    have hiff := hsideSeam edge hedge dart hdart (Or.inl hleft)
    exact (filledFaceComponentSide_iff_of_not_mem hright).1
      (hiff.mp (Or.inl hleft))
  · intro hright hleft
    have hiff := hsideSeam edge hedge dart hdart (Or.inr hright)
    exact (filledFaceComponentSide_iff_of_not_mem hleft).1
      (hiff.mpr (Or.inl hright))

/-!
The existential `faceComponentSide` is intentionally not used as the
definition of a primal side at a wall vertex: a wall vertex can see faces on
both sides.  The exact binary face cut already supplies the missing canonical
choice.  We record it as the label of an incident dart whose edge is not in
the wall.  At a cubic wall vertex there is one such port; away from the wall,
the local label-coherence theorem makes the choice independent of the dart.

This is a generic, route-neutral bridge.  It does not assert the Jordan
construction or the two side cycles; it isolates precisely the local premise
which that construction must provide.
-/

def exactCutLabelSide
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (wall : Finset E)
    (labels : OrbitFace RS → F2) (selected : F2) (vertex : V) : Prop :=
  ∃ dart : RS.D,
    RS.vertOf dart = vertex ∧
      RS.edgeOf dart ∉ wall ∧
        labels (dartOrbitFace RS dart) = selected

theorem exactCutLabelSide_iff_of_nonwall_dart_of_local_label_coherence
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (wall : Finset E)
    (labels : OrbitFace RS → F2) (selected : F2)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        RS.edgeOf dart ∈ wall)
    (hcoherent : ∀ {first second : RS.D},
      RS.vertOf second = RS.vertOf first →
      RS.edgeOf first ∉ wall →
      RS.edgeOf second ∉ wall →
      labels (dartOrbitFace RS first) =
        labels (dartOrbitFace RS second))
    (dart : RS.D) (haway : RS.edgeOf dart ∉ wall) :
    exactCutLabelSide RS wall labels selected (RS.vertOf dart) ↔
      exactCutLabelSide RS wall labels selected
        (RS.vertOf (RS.alpha dart)) := by
  constructor
  · rintro ⟨incident, hincident, hincidentAway, hselected⟩
    have hsame :
        labels (dartOrbitFace RS incident) =
          labels (dartOrbitFace RS dart) :=
      hcoherent hincident.symm hincidentAway haway
    have halpha :
        labels (dartOrbitFace RS dart) =
          labels (dartOrbitFace RS (RS.alpha dart)) :=
      GoertzelV24FaceCutTransport.labels_eq_alpha_of_not_cut
        RS labels (fun edge => edge ∈ wall) hexact dart haway
    refine ⟨RS.alpha dart, rfl, ?_, ?_⟩
    · simpa only [RS.edge_alpha] using haway
    · exact (hselected.symm.trans (hsame.trans halpha)).symm
  · rintro ⟨incident, hincident, hincidentAway, hselected⟩
    have hsame :
        labels (dartOrbitFace RS incident) =
          labels (dartOrbitFace RS (RS.alpha dart)) :=
      hcoherent hincident.symm hincidentAway (by
        simpa only [RS.edge_alpha] using haway)
    have halpha :
        labels (dartOrbitFace RS (RS.alpha dart)) =
          labels (dartOrbitFace RS dart) :=
      by
        simpa only [RS.alpha_involutive] using
          (GoertzelV24FaceCutTransport.labels_eq_alpha_of_not_cut
            RS labels (fun edge => edge ∈ wall) hexact (RS.alpha dart) (by
              simpa only [RS.edge_alpha] using haway))
    refine ⟨dart, rfl, haway, ?_⟩
    exact halpha.symm.trans (hsame.symm.trans hselected)

theorem labels_eq_of_same_vertex_of_unique_nonwall_port
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (wall : Finset E)
    (labels : OrbitFace RS → F2)
    {external first second : RS.D}
    (hunique : ∀ incident : RS.D,
      RS.vertOf incident = RS.vertOf external →
      incident ≠ external → RS.edgeOf incident ∈ wall)
    (hfirstBase : RS.vertOf first = RS.vertOf external)
    (hsecondBase : RS.vertOf second = RS.vertOf external)
    (hfirstAway : RS.edgeOf first ∉ wall)
    (hsecondAway : RS.edgeOf second ∉ wall) :
    labels (dartOrbitFace RS first) =
      labels (dartOrbitFace RS second) := by
  have hfirstEq : first = external := by
    by_contra hne
    exact hfirstAway (hunique first hfirstBase hne)
  have hsecondEq : second = external := by
    by_contra hne
    exact hsecondAway (hunique second hsecondBase hne)
  subst first
  subst second
  rfl

theorem labels_eq_of_same_vertex_of_all_incident_edges_not_wall
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E)
    (hrotation : VertexRotationCyclic RS)
    (wall : Finset E) (labels : OrbitFace RS → F2)
    (hexact : ∀ dart : RS.D,
      labels (dartOrbitFace RS dart) ≠
          labels (dartOrbitFace RS (RS.alpha dart)) ↔
        RS.edgeOf dart ∈ wall)
    {first second : RS.D}
    (hbase : RS.vertOf second = RS.vertOf first)
    (hnot : ∀ incident : RS.D,
      RS.vertOf incident = RS.vertOf first →
      RS.edgeOf incident ∉ wall) :
    labels (dartOrbitFace RS first) =
      labels (dartOrbitFace RS second) :=
  GoertzelV24FaceCutVertexAvoidingTransport.labels_eq_of_same_vertex_of_all_edges_not_cut
    RS hrotation labels (fun edge => edge ∈ wall) hexact first second hbase hnot

/-! The off-support half of the chord-side local coherence field. -/

theorem chord_labels_eq_of_same_vertex_off_cycleWalk_support
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    {vertex : V} (hvertex : vertex ∉ chord.cycleWalk.support)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {firstDart secondDart : embedded.RS.D}
    (hfirst : embedded.RS.vertOf firstDart = vertex)
    (hsecond : embedded.RS.vertOf secondDart = vertex) :
    labels (dartOrbitFace embedded.RS firstDart) =
      labels (dartOrbitFace embedded.RS secondDart) := by
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  apply labels_eq_of_same_vertex_of_all_incident_edges_not_wall
    embedded.RS hrotation (chord.boundary htriple).wall labels
  · intro dart
    rw [chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple]
    exact hexact dart
  · exact hsecond.trans hfirst.symm
  · intro incident hincident hwall
    have hnotCycle :=
      chord.toRotationSystem_edge_not_mem_cycleWalk_of_vertex_not_mem_support
        embedded.cellulation.rotation hvertex incident (hincident.trans hfirst)
    exact hnotCycle ((chord.mem_boundary_wall_iff_mem_cycleWalk_edges
      htriple (embedded.RS.edgeOf incident)).1 hwall)

theorem labels_eq_of_same_vertex_of_chord_cycle_turn_of_nonwall_darts
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
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
    (labels : OrbitFace embedded.RS → F2)
    {firstDart secondDart : embedded.RS.D}
    (hfirstBase : embedded.RS.vertOf firstDart =
      embedded.RS.vertOf external)
    (hsecondBase : embedded.RS.vertOf secondDart =
      embedded.RS.vertOf external)
    (hfirstAway : embedded.RS.edgeOf firstDart ∉
      (chord.boundary htriple).wall)
    (hsecondAway : embedded.RS.edgeOf secondDart ∉
      (chord.boundary htriple).wall) :
    labels (dartOrbitFace embedded.RS firstDart) =
      labels (dartOrbitFace embedded.RS secondDart) := by
  exact labels_eq_of_same_vertex_of_unique_nonwall_port
    embedded.RS (chord.boundary htriple).wall labels
    (all_other_incident_edges_in_wall_of_chord_cycle_turn
      embedded chord htriple hdata hprevious hcycleDart hbase hnonback
        external hexternalVertex haway)
    hfirstBase hsecondBase hfirstAway hsecondAway

/-! The existing cycle-transport theorem supplies the positive side cycle
once the selected seed face is known to touch the chord wall. -/

theorem hasCycleOnSide_of_faceComponentSide_chord_cycle
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)))
    (hseed :
      (faceAdjacencyAvoiding
        (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        (chord.boundary htriple).wall).Reachable
        seed
        (orbitFaceVertex embedded.RS
          (chord.cycleWalk.firstDart
            (chord.cycleWalk_isCycle htriple).not_nil))) :
    HasCycleOnSide G
      (faceComponentSide embedded.RS
        (chord.boundary htriple).wall seed) := by
  apply SimpleGraphDartRotation.Data.hasCycleOnSide_of_faceComponentSide_cycle
    embedded.cellulation.rotation chord.cycleWalk
      (chord.cycleWalk_isCycle htriple)
      (hasCyclicVertexRotations_implies_vertexRotationCyclic
        G embedded.cellulation.rotation
          embedded.cellulation.vertexRotation_cyclic)
      htwoSided
  · intro dart hdart
    exact cycleWalk_dartsAt_card_eq_three
      embedded hdata chord htriple dart hdart
  · intro edge
    exact chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge
  · exact hseed

/-! Filling the wall vertices only enlarges the selected side, so the same
positive cycle remains a witness for the filled primal predicate.  This is a
pure transport fact; it does not discharge the opposite-side/Jordan premise.
-/

theorem hasCycleOnSide_of_filledFaceComponentSide_chord_cycle
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (htwoSided : OrbitFacesTwoSided embedded.RS)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace embedded.RS)))
    (hseed :
      (faceAdjacencyAvoiding
        (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        (chord.boundary htriple).wall).Reachable
        seed
        (orbitFaceVertex embedded.RS
          (chord.cycleWalk.firstDart
            (chord.cycleWalk_isCycle htriple).not_nil))) :
    HasCycleOnSide G
      (filledFaceComponentSide chord.cycleWalk.support
        (faceComponentSide embedded.RS
          (chord.boundary htriple).wall seed)) := by
  apply HasCycleOnSide.mono
  · intro vertex hvertex
    exact Or.inr hvertex
  · exact hasCycleOnSide_of_faceComponentSide_chord_cycle
      embedded hdata chord htriple htwoSided seed hseed

/-! Any wall vertex can be based at a consecutive pair of cycle darts.  The
rotated cycle makes the predecessor/successor choice canonical; the cycle
nondegeneracy supplies the required nonbacktracking fact. -/

theorem exists_chord_cycle_turn_at_vertex_of_external_port
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    {vertex : V} (hvertex : vertex ∈ chord.cycleWalk.support)
    (external : embedded.RS.D)
    (hexternalVertex : embedded.RS.vertOf external = vertex)
    (_haway : embedded.RS.edgeOf external ∉
      (chord.boundary htriple).wall) :
    ∃ (previous cycleDart : embedded.RS.D),
      previous ∈ chord.cycleWalk.darts ∧
      cycleDart ∈ chord.cycleWalk.darts ∧
      embedded.RS.vertOf cycleDart =
        embedded.RS.vertOf (embedded.RS.alpha previous) ∧
      embedded.RS.alpha previous ≠ cycleDart ∧
      embedded.RS.vertOf external = embedded.RS.vertOf cycleDart := by
  let rotated := chord.cycleWalk.rotate vertex hvertex
  have hrotCycle : rotated.IsCycle := by
    exact (SimpleGraph.Walk.isCycle_rotate hvertex).2
      (chord.cycleWalk_isCycle htriple)
  have hrotNil : ¬ rotated.Nil := hrotCycle.not_nil
  let previous : embedded.RS.D := rotated.lastDart hrotNil
  let cycleDart : embedded.RS.D := rotated.firstDart hrotNil
  have hrotDarts : rotated.darts ~r chord.cycleWalk.darts := by
    exact chord.cycleWalk.rotate_darts vertex hvertex
  have hpreviousRot : previous ∈ rotated.darts := by
    exact rotated.lastDart_mem_darts hrotNil
  have hcycleDartRot : cycleDart ∈ rotated.darts := by
    exact rotated.firstDart_mem_darts hrotNil
  have hprevious : previous ∈ chord.cycleWalk.darts := by
    exact (hrotDarts.mem_iff).1 hpreviousRot
  have hcycleDart : cycleDart ∈ chord.cycleWalk.darts := by
    exact (hrotDarts.mem_iff).1 hcycleDartRot
  have hbase : embedded.RS.vertOf cycleDart =
      embedded.RS.vertOf (embedded.RS.alpha previous) := by
    change cycleDart.fst = (embedded.RS.alpha previous).fst
    change (rotated.firstDart hrotNil).fst =
      (SimpleGraph.Dart.symm (rotated.lastDart hrotNil)).fst
    rfl
  have hnonback : embedded.RS.alpha previous ≠ cycleDart := by
    intro heq
    have hbad : rotated.penultimate = rotated.snd := by
      have hsnd := congrArg (fun dart : embedded.RS.D => dart.snd) heq
      simpa [previous, cycleDart, SimpleGraph.Walk.firstDart,
        SimpleGraph.Walk.lastDart] using hsnd
    exact hrotCycle.snd_ne_penultimate hbad.symm
  refine ⟨previous, cycleDart, hprevious, hcycleDart, hbase, hnonback, ?_⟩
  change external.fst = cycleDart.fst
  simpa [cycleDart, SimpleGraph.Walk.firstDart] using hexternalVertex

theorem exists_external_port_dart_at_chord_cycle_vertex
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (edge : G.edgeSet) (hedge : edge.1 ∈ chord.cycleWalk.edges)
    {vertex : V} (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    ∃ port : embedded.RS.D,
      embedded.RS.vertOf port = vertex ∧
      embedded.RS.edgeOf port ∉ (chord.boundary htriple).wall := by
  rcases chord.exists_external_port_at_cycleWalk_vertex hdata hC htriple
      edge hedge hvertex with
    ⟨port, hportVertex, hportOutside⟩
  obtain ⟨dart, hdart⟩ := embedded.RS.dartsOn_nonempty port
  have hendpoints : embedded.RS.endpoints port =
      {embedded.RS.vertOf dart,
        embedded.RS.vertOf (embedded.RS.alpha dart)} :=
    embedded.RS.endpoints_eq_pair_of_mem hdart
  have hvertexEndpoints : vertex ∈ embedded.RS.endpoints port := by
    exact (mem_simpleGraphRotationSystem_endpoints_iff
      embedded.cellulation.rotation port vertex).2 hportVertex
  have hvertexCases : vertex = embedded.RS.vertOf dart ∨
      vertex = embedded.RS.vertOf (embedded.RS.alpha dart) := by
    rw [hendpoints] at hvertexEndpoints
    simpa using hvertexEndpoints
  have hdartEdge : embedded.RS.edgeOf dart = port :=
    embedded.RS.mem_dartsOn.mp hdart
  have hportAway : embedded.RS.edgeOf dart ∉
      (chord.boundary htriple).wall := by
    intro hwall
    rw [hdartEdge] at hwall
    apply hportOutside
    exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges
      htriple port).1 hwall
  rcases hvertexCases with hvertexDart | hvertexAlpha
  · refine ⟨dart, hvertexDart.symm, hportAway⟩
  · refine ⟨embedded.RS.alpha dart, hvertexAlpha.symm, ?_⟩
    simpa only [embedded.RS.edge_alpha] using hportAway

/-! The interval-level external-port certificate can be lifted uniformly to
both endpoints of any wall edge.  This is the reusable incidence half of the
primal seam; it deliberately says nothing yet about the labels of the two
ports or about cycles on either side. -/
theorem exists_external_ports_at_wall_edge_endpoints
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (edge : G.edgeSet) (hedge : edge ∈ (chord.boundary htriple).wall)
    {u v : V} (hu : u ∈ (edge : Sym2 V))
    (hv : v ∈ (edge : Sym2 V)) :
    ∃ (portU portV : embedded.RS.D),
      embedded.RS.vertOf portU = u ∧
      embedded.RS.vertOf portV = v ∧
      embedded.RS.edgeOf portU ∉ (chord.boundary htriple).wall ∧
      embedded.RS.edgeOf portV ∉ (chord.boundary htriple).wall := by
  have hcycleEdge : edge.1 ∈ chord.cycleWalk.edges :=
    (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).1 hedge
  rcases exists_external_port_dart_at_chord_cycle_vertex
      embedded hdata hC chord htriple edge hcycleEdge hu with
    ⟨portU, hportU, hportUAway⟩
  rcases exists_external_port_dart_at_chord_cycle_vertex
      embedded hdata hC chord htriple edge hcycleEdge hv with
    ⟨portV, hportV, hportVAway⟩
  exact ⟨portU, portV, hportU, hportV, hportUAway, hportVAway⟩

theorem chord_labels_eq_of_same_vertex_on_cycleWalk_support
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    {vertex : V} (hvertex : vertex ∈ chord.cycleWalk.support)
    (labels : OrbitFace embedded.RS → F2)
    {firstDart secondDart : embedded.RS.D}
    (hfirst : embedded.RS.vertOf firstDart = vertex)
    (hsecond : embedded.RS.vertOf secondDart = vertex)
    (hfirstAway : embedded.RS.edgeOf firstDart ∉
      (chord.boundary htriple).wall)
    (hsecondAway : embedded.RS.edgeOf secondDart ∉
      (chord.boundary htriple).wall) :
    labels (dartOrbitFace embedded.RS firstDart) =
      labels (dartOrbitFace embedded.RS secondDart) := by
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  rcases (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
      hcycle.not_nil).1 hvertex with
    ⟨edgeValue, hedgeValue, hvertexEdge⟩
  let edge : G.edgeSet :=
    ⟨edgeValue, chord.cycleWalk.edges_subset_edgeSet hedgeValue⟩
  rcases exists_external_port_dart_at_chord_cycle_vertex
      embedded hdata hC chord htriple edge hedgeValue hvertexEdge with
    ⟨external, hexternalVertex, haway⟩
  rcases exists_chord_cycle_turn_at_vertex_of_external_port
      embedded chord htriple hvertex external hexternalVertex haway with
    ⟨previous, cycleDart, hprevious, hcycleDart, hbase, hnonback,
      hexternalCycleDart⟩
  exact labels_eq_of_same_vertex_of_chord_cycle_turn_of_nonwall_darts
    embedded hdata chord htriple hprevious hcycleDart hbase hnonback
      external hexternalCycleDart haway labels
      (hfirst.trans hexternalVertex.symm)
      (hsecond.trans hexternalVertex.symm) hfirstAway hsecondAway

theorem chord_labels_eq_of_same_vertex_of_nonwall_darts
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {firstDart secondDart : embedded.RS.D}
    (hbase : embedded.RS.vertOf secondDart =
      embedded.RS.vertOf firstDart)
    (hfirstAway : embedded.RS.edgeOf firstDart ∉
      (chord.boundary htriple).wall)
    (hsecondAway : embedded.RS.edgeOf secondDart ∉
      (chord.boundary htriple).wall) :
    labels (dartOrbitFace embedded.RS firstDart) =
      labels (dartOrbitFace embedded.RS secondDart) := by
  by_cases hvertex : embedded.RS.vertOf firstDart ∈ chord.cycleWalk.support
  · exact chord_labels_eq_of_same_vertex_on_cycleWalk_support
      embedded hdata hC chord htriple hvertex labels rfl hbase
        hfirstAway hsecondAway
  · exact chord_labels_eq_of_same_vertex_off_cycleWalk_support
      embedded chord htriple hvertex labels hexact
      rfl hbase

theorem exactCutLabelSide_iff_of_nonwall_chord_dart
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2) (selected : F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (dart : embedded.RS.D)
    (haway : embedded.RS.edgeOf dart ∉
      (chord.boundary htriple).wall) :
    exactCutLabelSide embedded.RS (chord.boundary htriple).wall
        labels selected (embedded.RS.vertOf dart) ↔
      exactCutLabelSide embedded.RS (chord.boundary htriple).wall
        labels selected (embedded.RS.vertOf (embedded.RS.alpha dart)) := by
  have hexactWall : ∀ candidate : embedded.RS.D,
      labels (dartOrbitFace embedded.RS candidate) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha candidate)) ↔
        embedded.RS.edgeOf candidate ∈ (chord.boundary htriple).wall := by
    intro candidate
    rw [chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple]
    exact hexact candidate
  apply exactCutLabelSide_iff_of_nonwall_dart_of_local_label_coherence
    embedded.RS (chord.boundary htriple).wall labels selected hexactWall
  · intro firstDart secondDart hbase hfirstAway hsecondAway
    exact chord_labels_eq_of_same_vertex_of_nonwall_darts
      embedded hdata hC chord htriple labels hexact hbase
        hfirstAway hsecondAway
  · exact haway

theorem exactCutLabelSide_iff_of_nonwall_chord_edge
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2) (selected : F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {edge : G.edgeSet} (haway : edge ∉
      (chord.boundary htriple).wall)
    {u v : V} (hu : u ∈ (edge : Sym2 V))
    (hv : v ∈ (edge : Sym2 V)) :
    exactCutLabelSide embedded.RS (chord.boundary htriple).wall
        labels selected u ↔
      exactCutLabelSide embedded.RS (chord.boundary htriple).wall
        labels selected v := by
  obtain ⟨dart, hdart⟩ := embedded.RS.dartsOn_nonempty edge
  have hdartEdge : embedded.RS.edgeOf dart = edge :=
    embedded.RS.mem_dartsOn.mp hdart
  have hdartAway : embedded.RS.edgeOf dart ∉
      (chord.boundary htriple).wall := by
    rw [hdartEdge]
    exact haway
  have hdartEndpoints : embedded.RS.endpoints edge =
      {embedded.RS.vertOf dart,
        embedded.RS.vertOf (embedded.RS.alpha dart)} :=
    embedded.RS.endpoints_eq_pair_of_mem hdart
  have huEndpoints : u ∈ embedded.RS.endpoints edge := by
    exact (mem_simpleGraphRotationSystem_endpoints_iff
      embedded.cellulation.rotation edge u).2 hu
  have hvEndpoints : v ∈ embedded.RS.endpoints edge := by
    exact (mem_simpleGraphRotationSystem_endpoints_iff
      embedded.cellulation.rotation edge v).2 hv
  have huCases : u = embedded.RS.vertOf dart ∨
      u = embedded.RS.vertOf (embedded.RS.alpha dart) := by
    rw [hdartEndpoints] at huEndpoints
    simpa using huEndpoints
  have hvCases : v = embedded.RS.vertOf dart ∨
      v = embedded.RS.vertOf (embedded.RS.alpha dart) := by
    rw [hdartEndpoints] at hvEndpoints
    simpa using hvEndpoints
  have hsideDart := exactCutLabelSide_iff_of_nonwall_chord_dart
    embedded hdata hC chord htriple labels selected hexact dart hdartAway
  rcases huCases with huD | huA <;>
    rcases hvCases with hvD | hvA
  · simpa [huD, hvD] using hsideDart
  · simpa [huD, hvA] using hsideDart
  · simpa [huA, hvD] using hsideDart.symm
  · simpa [huA, hvA] using hsideDart.symm

theorem exactCutLabelSide_iff_of_chord_port
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2) (selected : F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {vertex : V} (port : embedded.RS.D)
    (hportVertex : embedded.RS.vertOf port = vertex)
    (hportAway : embedded.RS.edgeOf port ∉
      (chord.boundary htriple).wall) :
    exactCutLabelSide embedded.RS (chord.boundary htriple).wall
        labels selected vertex ↔
      labels (dartOrbitFace embedded.RS port) = selected := by
  constructor
  · rintro ⟨incident, hincident, hincidentAway, hselected⟩
    have hlabels := chord_labels_eq_of_same_vertex_of_nonwall_darts
      embedded hdata hC chord htriple labels hexact
      (hportVertex.trans hincident.symm) hincidentAway hportAway
    exact hlabels.symm.trans hselected
  · intro hselected
    exact ⟨port, hportVertex, hportAway, hselected⟩

theorem edgeCrossesVertexSide_of_f2_label_inequality
    {e : G.edgeSet} {u v : V}
    {side : V → Prop} {labelU labelV selected : F2}
    (hu : u ∈ (e : Sym2 V)) (hv : v ∈ (e : Sym2 V))
    (hsideU : side u ↔ labelU = selected)
    (hsideV : side v ↔ labelV = selected)
    (hlabels : labelU ≠ labelV) :
    EdgeCrossesVertexSide G side e := by
  by_cases hsu : side u
  · by_cases hsv : side v
    · exfalso
      apply hlabels
      exact (hsideU.mp hsu).trans (hsideV.mp hsv).symm
    · exact ⟨u, v, hu, hv, hsu, hsv⟩
  · by_cases hsv : side v
    · exact ⟨v, u, hv, hu, hsv, hsu⟩
    · exfalso
      have hlabelUne : labelU ≠ selected := by
        intro heq
        exact hsu (hsideU.mpr heq)
      have hlabelVne : labelV ≠ selected := by
        intro heq
        exact hsv (hsideV.mpr heq)
      have heq : labelU = labelV := by
        fin_cases labelU <;> fin_cases labelV <;> fin_cases selected <;>
          simp_all
      exact hlabels heq

/-! The exact-cut equation already supplies the port-label inequality once
the planar turn has identified the two endpoint ports with the two incident
faces of an oriented wall dart.  Keeping this adapter separate is useful:
the remaining Jordan argument only has to produce those two face
identifications, rather than reproving the binary-label step at every wall
edge. -/

theorem labels_ne_of_exact_cut_of_wall_dart_face_assignment
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {wallDart portU portV : embedded.RS.D}
    (hwallDart : (embedded.RS.edgeOf wallDart).1 ∈
      chord.cycleWalk.edges)
    (hportUFace : dartOrbitFace embedded.RS portU =
      dartOrbitFace embedded.RS wallDart)
    (hportVFace : dartOrbitFace embedded.RS portV =
      dartOrbitFace embedded.RS (embedded.RS.alpha wallDart)) :
    labels (dartOrbitFace embedded.RS portU) ≠
      labels (dartOrbitFace embedded.RS portV) := by
  intro hlabels
  apply (hexact wallDart).2 hwallDart
  calc
    labels (dartOrbitFace embedded.RS wallDart) =
        labels (dartOrbitFace embedded.RS portU) := by
      rw [hportUFace]
    _ = labels (dartOrbitFace embedded.RS portV) := hlabels
    _ = labels (dartOrbitFace embedded.RS
        (embedded.RS.alpha wallDart)) := by
      rw [hportVFace]

/-! The preceding binary-label lemma is the local end of the wall seam.  The
following adapter gives the geometric caller one named obligation: for each
wall edge, identify an oriented wall dart and the two off-wall endpoint ports
with its two incident faces.  Once that obligation is supplied, exact-cut
transport produces the label packet consumed by the crossing theorem.  No
Jordan or side-separation claim is hidden in this adapter. -/

theorem wall_port_label_packet_of_wall_dart_face_assignment
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (hfaceAssignment : ∀ (edge : G.edgeSet),
      edge ∈ (chord.boundary htriple).wall →
      ∀ {u v : V}, u ∈ (edge : Sym2 V) → v ∈ (edge : Sym2 V) →
      ∃ (wallDart portU portV : embedded.RS.D),
        embedded.RS.edgeOf wallDart = edge ∧
        embedded.RS.vertOf portU = u ∧
        embedded.RS.vertOf portV = v ∧
        embedded.RS.edgeOf portU ∉ (chord.boundary htriple).wall ∧
        embedded.RS.edgeOf portV ∉ (chord.boundary htriple).wall ∧
        dartOrbitFace embedded.RS portU =
          dartOrbitFace embedded.RS wallDart ∧
        dartOrbitFace embedded.RS portV =
          dartOrbitFace embedded.RS (embedded.RS.alpha wallDart)) :
    ∀ (edge : G.edgeSet), edge ∈ (chord.boundary htriple).wall →
      ∀ {u v : V}, u ∈ (edge : Sym2 V) → v ∈ (edge : Sym2 V) →
      ∃ (portU portV : embedded.RS.D),
        embedded.RS.vertOf portU = u ∧
        embedded.RS.vertOf portV = v ∧
        embedded.RS.edgeOf portU ∉ (chord.boundary htriple).wall ∧
        embedded.RS.edgeOf portV ∉ (chord.boundary htriple).wall ∧
        labels (dartOrbitFace embedded.RS portU) ≠
          labels (dartOrbitFace embedded.RS portV) := by
  intro edge hedge u v hu hv
  rcases hfaceAssignment edge hedge hu hv with
    ⟨wallDart, portU, portV, hwallDartEdge, hportU, hportV,
      hportUAway, hportVAway, hportUFace, hportVFace⟩
  refine ⟨portU, portV, hportU, hportV, hportUAway, hportVAway, ?_⟩
  apply labels_ne_of_exact_cut_of_wall_dart_face_assignment
    embedded chord labels hexact
      (wallDart := wallDart) (portU := portU) (portV := portV)
  rw [hwallDartEdge]
  exact (chord.mem_boundary_wall_iff_mem_cycleWalk_edges htriple edge).1 hedge
  · exact hportUFace
  · exact hportVFace

theorem edgeCrossesVertexSide_of_chord_wall_of_port_label_inequality
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2) (selected : F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    {edge : G.edgeSet} (_hedge : edge ∈
      (chord.boundary htriple).wall)
    {u v : V} (hu : u ∈ (edge : Sym2 V))
    (hv : v ∈ (edge : Sym2 V))
    (portU portV : embedded.RS.D)
    (hportU : embedded.RS.vertOf portU = u)
    (hportV : embedded.RS.vertOf portV = v)
    (hportUAway : embedded.RS.edgeOf portU ∉
      (chord.boundary htriple).wall)
    (hportVAway : embedded.RS.edgeOf portV ∉
      (chord.boundary htriple).wall)
    (hlabels : labels (dartOrbitFace embedded.RS portU) ≠
      labels (dartOrbitFace embedded.RS portV)) :
    EdgeCrossesVertexSide G
      (exactCutLabelSide embedded.RS (chord.boundary htriple).wall
        labels selected) edge := by
  apply edgeCrossesVertexSide_of_f2_label_inequality hu hv
  · exact exactCutLabelSide_iff_of_chord_port
      embedded hdata hC chord htriple labels selected hexact
        portU hportU hportUAway
  · exact exactCutLabelSide_iff_of_chord_port
      embedded hdata hC chord htriple labels selected hexact
        portV hportV hportVAway
  · exact hlabels

noncomputable def cyclicEdgeCutRealization_of_exactCutLabelSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2) (selected : F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (hcut_crosses : ∀ edge : G.edgeSet,
      edge ∈ (chord.boundary htriple).wall →
      EdgeCrossesVertexSide G
        (exactCutLabelSide embedded.RS (chord.boundary htriple).wall
          labels selected) edge)
    (hinside_cycle : HasCycleOnSide G
      (exactCutLabelSide embedded.RS (chord.boundary htriple).wall
        labels selected))
    (houtside_cycle : HasCycleOnSide G
      (fun vertex => ¬ exactCutLabelSide embedded.RS
        (chord.boundary htriple).wall labels selected vertex)) :
    CyclicEdgeCutRealization G (chord.boundary htriple).wall := by
  refine CyclicEdgeCutRealization.of_edge_side_classification
    (exactCutLabelSide embedded.RS (chord.boundary htriple).wall
      labels selected) hcut_crosses ?_ hinside_cycle houtside_cycle
  intro edge hnot u v hu hv
  exact exactCutLabelSide_iff_of_nonwall_chord_edge
    embedded hdata hC chord htriple labels selected hexact hnot hu hv

/-! The global crossing premise for the exact label side can be discharged
from a finite local packet at the wall: each wall edge has an off-wall dart at
each endpoint, and the two corresponding face labels differ.  This theorem
keeps the remaining Jordan/separation work honest and explicit; it does not
silently manufacture the endpoint ports or their label inequality. -/
noncomputable def cyclicEdgeCutRealization_of_exactCutLabelSide_of_wall_port_label_packet
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} (hC : IsTaitEdgeColoring G C)
    {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2) (selected : F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (hports : ∀ (edge : G.edgeSet),
      edge ∈ (chord.boundary htriple).wall →
      ∀ {u v : V}, u ∈ (edge : Sym2 V) → v ∈ (edge : Sym2 V) →
      ∃ (portU portV : embedded.RS.D),
        embedded.RS.vertOf portU = u ∧
        embedded.RS.vertOf portV = v ∧
        embedded.RS.edgeOf portU ∉ (chord.boundary htriple).wall ∧
        embedded.RS.edgeOf portV ∉ (chord.boundary htriple).wall ∧
        labels (dartOrbitFace embedded.RS portU) ≠
          labels (dartOrbitFace embedded.RS portV))
    (hinside_cycle : HasCycleOnSide G
      (exactCutLabelSide embedded.RS (chord.boundary htriple).wall
        labels selected))
    (houtside_cycle : HasCycleOnSide G
      (fun vertex => ¬ exactCutLabelSide embedded.RS
        (chord.boundary htriple).wall labels selected vertex)) :
    CyclicEdgeCutRealization G (chord.boundary htriple).wall := by
  refine cyclicEdgeCutRealization_of_exactCutLabelSide
    embedded hdata hC chord htriple labels selected hexact ?_
      hinside_cycle houtside_cycle
  intro edge hedge
  obtain ⟨dart, hdart⟩ := embedded.RS.dartsOn_nonempty edge
  have hu : embedded.RS.vertOf dart ∈ (edge : Sym2 V) := by
    apply (mem_simpleGraphRotationSystem_endpoints_iff
      embedded.cellulation.rotation edge (embedded.RS.vertOf dart)).1
    exact (embedded.RS.mem_endpoints_iff).2 ⟨dart, hdart, rfl⟩
  have hv : embedded.RS.vertOf (embedded.RS.alpha dart) ∈
      (edge : Sym2 V) := by
    apply (mem_simpleGraphRotationSystem_endpoints_iff
      embedded.cellulation.rotation edge
        (embedded.RS.vertOf (embedded.RS.alpha dart))).1
    exact (embedded.RS.mem_endpoints_iff).2
      ⟨embedded.RS.alpha dart, by simpa using hdart, rfl⟩
  rcases hports edge hedge hu hv with
    ⟨portU, portV, hportU, hportV, hportUAway, hportVAway, hlabels⟩
  exact edgeCrossesVertexSide_of_chord_wall_of_port_label_inequality
    embedded hdata hC chord htriple labels selected hexact hedge hu hv
      portU portV hportU hportV hportUAway hportVAway hlabels

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
